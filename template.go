package template

import (
	"errors"
	"fmt"
	"io"
	"reflect"
	"runtime"
	"sync"
	"text/template/parse"
)

var (
	boolType       = reflect.ValueOf(true).Type()
	stringType     = reflect.ValueOf("").Type()
	int64Type      = reflect.ValueOf(int64(0)).Type()
	uint64Type     = reflect.ValueOf(uint64(0)).Type()
	float64Type    = reflect.ValueOf(float64(0)).Type()
	complex128Type = reflect.ValueOf(complex128(0)).Type()
)

type state struct {
	w    io.Writer
	vars []variable // push-down stack of variable values
}

type variable struct {
	name  string
	value reflect.Value
}

func (s *state) push(name string, value reflect.Value) {
	panic(fmt.Sprintf("%s:=%s", name, value))
	s.vars = append(s.vars, variable{name, value})
}

func (s *state) mark() int {
	return len(s.vars)
}

func (s *state) pop(mark int) {
	s.vars = s.vars[0:mark]
}

func (s *state) setVar(n int, value reflect.Value) {
	s.vars[len(s.vars)-n].value = value
}

func (s *state) varValue(name string) reflect.Value {
	for i := s.mark() - 1; i >= 0; i-- {
		if s.vars[i].name == name {
			return s.vars[i].value
		}
	}
	panic(fmt.Errorf("undefined variable: %s", name))
}

type Template struct {
	*parse.Tree
	executor map[reflect.Type]executor
	m        sync.RWMutex
}

func Must(t *Template, err error) *Template {
	if err != nil {
		panic(err)
	}
	return t
}

func New() *Template {
	return &Template{
		executor: make(map[reflect.Type]executor),
	}
}

func (t *Template) Parse(s string) (*Template, error) {
	fs := map[string]interface{}{
		"print1": print1,
	}
	m, err := parse.Parse("name", s, "{{", "}}", fs)
	if err != nil {
		return nil, err
	}
	t.Tree = m["name"]
	return t, nil
}

type executor func(s state, dot interface{})

type command func(s state, dot, final interface{}) interface{}
type filter func(s state, dot interface{}) interface{}
type lookupFn func(s state, v reflect.Value, final interface{}) reflect.Value

func errRecover(errp *error) {
	e := recover()
	if e != nil {
		switch err := e.(type) {
		case runtime.Error:
			panic(e)
		case error:
			*errp = err
		default:
			panic(e)
		}
	}
}

func (t *Template) Execute(w io.Writer, dot interface{}) (err error) {
	defer errRecover(&err)

	value := reflect.ValueOf(dot)
	var typ reflect.Type
	if value.IsValid() {
		typ = value.Type()
	}

	t.m.RLock()
	f, exist := t.executor[typ]
	t.m.RUnlock()
	if !exist {
		f = compile(t.Tree.Root, typ)
		t.m.Lock()
		t.executor[typ] = f
		t.m.Unlock()
	}

	s := state{w, []variable{{"$", value}}}
	f(s, dot)
	return nil
}

func stringer(t reflect.Type) func(v interface{}) string {
	if t == nil {
		return stringerDynamic()
	}
	switch t.Kind() {
	case reflect.String:
		return func(v interface{}) string { return v.(string) }
	case reflect.Bool:
		return func(v interface{}) string {
			if v.(bool) {
				return "true"
			}
			return "false"
		}
	case reflect.Int, reflect.Uint, reflect.Int64, reflect.Uint64, reflect.Float64, reflect.Complex128:
		return func(v interface{}) string { return fmt.Sprint(v) }
	case reflect.Interface:
		return stringerDynamic()
	default:
		panic(fmt.Errorf("stringer: %s", t.Kind()))
	}
}

func stringerDynamic() func(v interface{}) string {
	var m sync.RWMutex
	cache := make(map[reflect.Type]func(interface{}) string)
	return func(v interface{}) string {
		typ := reflect.ValueOf(v).Type()
		m.RLock()
		f, exist := cache[typ]
		m.RUnlock()
		if !exist {
			f = stringer(typ)
			m.Lock()
			cache[typ] = f
			m.Unlock()
		}
		return f(v)
	}
}

func booler(t reflect.Type) func(v interface{}) bool {
	switch t.Kind() {
	case reflect.String:
		return func(v interface{}) bool { return v.(string) != "" }
	case reflect.Bool:
		return func(v interface{}) bool { return v.(bool) }
	case reflect.Int:
		return func(v interface{}) bool { return v.(int) != 0 }
	case reflect.Uint:
		return func(v interface{}) bool { return v.(uint) != 0 }
	case reflect.Int64:
		return func(v interface{}) bool { return v.(int64) != 0 }
	case reflect.Uint64:
		return func(v interface{}) bool { return v.(uint64) != 0 }
	case reflect.Float64:
		return func(v interface{}) bool { return v.(float64) != 0 }
	case reflect.Complex128:
		return func(v interface{}) bool { return v.(complex128) != 0 }
	case reflect.Chan, reflect.Func, reflect.Ptr, reflect.Interface:
		return func(v interface{}) bool { return !reflect.ValueOf(v).IsNil() }
	case reflect.Map, reflect.Array, reflect.Slice:
		return func(v interface{}) bool { return reflect.ValueOf(v).Len() > 0 }
	case reflect.Struct:
		return func(interface{}) bool { return true }
	default:
		return func(interface{}) bool { return false }
	}
}

func compile(node parse.Node, typ reflect.Type) executor {
	switch node := node.(type) {
	case *parse.ActionNode:
		f, final := compilePipeline(node.Pipe, typ)
		toString := stringer(final)
		return func(s state, dot interface{}) {
			r := f(s, dot)
			if len(node.Pipe.Decl) == 0 {
				io.WriteString(s.w, toString(r))
			}
		}
	case *parse.ListNode:
		var fs []executor
		for _, m := range node.Nodes {
			fs = append(fs, compile(m, typ))
		}
		return func(s state, dot interface{}) {
			for _, f := range fs {
				f(s, dot)
			}
		}
	case *parse.IfNode:
		return compileBranch(&node.BranchNode, typ, parse.NodeIf)
	case *parse.WithNode:
		return compileBranch(&node.BranchNode, typ, parse.NodeWith)
	case *parse.PipeNode:
	case *parse.TextNode:
		return func(s state, _ interface{}) {
			_, err := s.w.Write(node.Text)
			if err != nil {
				panic(fmt.Errorf("TextNode: %s", err))
			}
		}
	}
	panic(fmt.Errorf("Unsupported type %T\n", node))
}

func compilePipeline(node *parse.PipeNode, typ reflect.Type) (filter, reflect.Type) {
	var fs []command
	var final reflect.Type
	for _, cmd := range node.Cmds {
		var f command
		f, final = compileCommand(cmd, typ, final)
		fs = append(fs, f)
	}
	f := func(s state, dot interface{}) interface{} {
		var v interface{}
		for _, f := range fs {
			v = f(s, dot, v)
		}
		for _, variable := range node.Decl {
			s.push(variable.Ident[0], reflect.ValueOf(v))
		}
 		return v
	}
	return f, final
}

func compileFieldNode(node *parse.FieldNode, typ reflect.Type, args []parse.Node, final reflect.Type) (cmd command, retType reflect.Type) {
	return compileFieldChain(node.Ident, typ, args, final)
}

func compileFieldChain(ident []string, typ reflect.Type, args []parse.Node, final reflect.Type) (cmd command, retType reflect.Type) {
	var fs []lookupFn
	var f lookupFn
	for _, name := range ident[:len(ident)-1] {
		f, typ = compileField(typ, name, nil, nil)
		fs = append(fs, f)
	}
	f, typ = compileField(typ, ident[len(ident)-1], args[1:], final)
	fs = append(fs, f)
	cmd = func(s state, dot, final interface{}) interface{} {
		v := reflect.ValueOf(dot)
		for _, f := range fs[:len(fs)-1] {
			v = f(s, v, nil)
		}
		f := fs[len(fs)-1]
		v = f(s, v, final)
		return v.Interface()
	}
	retType = typ
	return
}

func compileCommand(node *parse.CommandNode, typ reflect.Type, final reflect.Type) (cmd command, retType reflect.Type) {
	firstWord := node.Args[0]
	switch n := firstWord.(type) {
	case *parse.FieldNode:
		return compileFieldNode(n, typ, node.Args, final)
	case *parse.IdentifierNode:
		return compileFunction(n, typ, node.Args, final)
	case *parse.PipeNode:
		var f filter
		f, retType = compilePipeline(n, typ)
		cmd = func(s state, dot, _ interface{}) interface{} { return f(s, dot) }
		return
	case *parse.VariableNode:
		return compileVariableNode(n, typ, node.Args, final)
	}
	if final != nil || len(node.Args) > 1 {
		panic(fmt.Errorf("can't give argument to non-function %s", node.Args[0]))
	}

	switch node := firstWord.(type) {
	case *parse.BoolNode:
		cmd = func(_ state, _, _ interface{}) interface{} { return node.True }
		retType = boolType
		return
	case *parse.DotNode:
		cmd = func(_ state, dot, _ interface{}) interface{} { return dot }
		retType = typ
		return
	case *parse.NilNode:
		panic(errors.New("nil is not a command"))
	case *parse.NumberNode:
		switch {
		case node.IsInt:
			cmd = func(_ state, _, _ interface{}) interface{} { return node.Int64 }
			retType = int64Type
		case node.IsUint:
			cmd = func(_ state, _, _ interface{}) interface{} { return node.Uint64 }
			retType = uint64Type
		case node.IsFloat:
			cmd = func(_ state, _, _ interface{}) interface{} { return node.Float64 }
			retType = float64Type
		case node.IsComplex:
			cmd = func(_ state, _, _ interface{}) interface{} { return node.Complex128 }
			retType = complex128Type
		default:
			panic(errors.New("invalid NumberNode"))
		}
		return
	case *parse.StringNode:
		cmd = func(_ state, _, _ interface{}) interface{} { return node.Text }
		retType = stringType
		return
	}
	panic(fmt.Errorf("can't evaluate command %t", node.Args[0]))
}

func compileBranch(node *parse.BranchNode, typ reflect.Type, nodeType parse.NodeType) executor {
	f, ftype := compilePipeline(node.Pipe, typ)
	toBool := booler(ftype)

	var list, elseList executor
	if nodeType == parse.NodeIf {
		list = compile(node.List, typ)
	} else {
		list = compile(node.List, ftype) // nodeType == parse.NodeWith
	}
	if node.ElseList != nil {
		elseList = compile(node.ElseList, typ)
	}

	return func(s state, dot interface{}) {
		cond := f(s, dot)
		if toBool(cond) {
			if nodeType == parse.NodeIf {
				list(s, dot)
			} else {
				list(s, cond) // nodeType == parse.NodeWith
			}
		} else if elseList != nil {
			elseList(s, dot)
		}
	}
}

func isNilType(t reflect.Type) bool {
	return t == nil || (t.Kind() == reflect.Interface && t.NumMethod() == 0)
}

func compileField(typ reflect.Type, name string, args []parse.Node, final reflect.Type) (fn lookupFn, elem reflect.Type) {
	if isNilType(typ) {
		fn = compileFieldDynamic(name, args)
		return
	}

	if m, exist := typ.MethodByName(name); exist {
		fn = compileMethodCall(typ, m.Func, args, final)
		elem = m.Type.Out(0)
		return
	}

	switch typ.Kind() {
	case reflect.Struct:
		structField, found := typ.FieldByName(name)
		if !found {
			panic(fmt.Errorf("%s has no field %s", typ, name))
		}
		fn = func(s state, v reflect.Value, final interface{}) reflect.Value {
			return v.FieldByIndex(structField.Index)
		}
		elem = structField.Type
		return
	case reflect.Map:
		k := reflect.ValueOf(name)
		fn = func(s state, v reflect.Value, final interface{}) reflect.Value {
			return v.MapIndex(k)
		}
		elem = typ.Key()
		return
	}
	panic(fmt.Errorf("struct or map expected, but got %s", typ))
}

func compileFieldDynamic(name string, args []parse.Node) lookupFn {
	type key struct {
		valueType reflect.Type
		finalType reflect.Type
	}

	var m sync.RWMutex
	cache := make(map[key]lookupFn)
	return func(s state, value reflect.Value, final interface{}) reflect.Value {
		valueType := value.Elem().Type()
		var finalType reflect.Type
		if v := reflect.ValueOf(final); v.IsValid() {
			finalType = v.Type()
		}

		k := key{valueType, finalType}
		m.RLock()
		f, exist := cache[k]
		m.RUnlock()
		if !exist {
			f, _ = compileField(valueType, name, args, finalType)
			m.Lock()
			cache[k] = f
			m.Unlock()
		}
		return f(s, value.Elem(), final)
	}
}

func compileMethodCall(typ reflect.Type, fun reflect.Value, args []parse.Node, finalType reflect.Type) lookupFn {
	fs := make([]filter, len(args))
	for i, v := range args {
		fs[i] = compileArg(typ, fun.Type().In(i+1), v)
	}
	return func(s state, dot reflect.Value, final interface{}) reflect.Value {
		l := len(fs) + 1
		if finalType != nil {
			l++
		}
		vs := make([]reflect.Value, l)
		vs[0] = dot
		for i, f := range fs {
			vs[i+1] = reflect.ValueOf(f(s, dot))
		}
		if finalType != nil {
			vs[len(vs)-1] = reflect.ValueOf(final)
		}
		r := fun.Call(vs)
		return r[0]
	}
}

func compileFuncCall(typ reflect.Type, fun reflect.Value, args []parse.Node, finalType reflect.Type) lookupFn {
	fs := make([]filter, len(args))
	for i, v := range args {
		fs[i] = compileArg(typ, fun.Type().In(i), v)
	}
	return func(s state, dot reflect.Value, final interface{}) reflect.Value {
		l := len(fs)
		if finalType != nil {
			l++
		}
		vs := make([]reflect.Value, l)
		for i, f := range fs {
			vs[i] = reflect.ValueOf(f(s, dot))
		}
		if finalType != nil {
			vs[len(vs)-1] = reflect.ValueOf(final)
		}
		r := fun.Call(vs)
		return r[0]
	}
}

func compileArg(dotType, argType reflect.Type, node parse.Node) filter {
	switch node := node.(type) {
	case *parse.DotNode:
		return func(s state, v interface{}) interface{} { return v }
	case *parse.NilNode:
		panic(fmt.Errorf("cannot assign nil to %s", dotType))
	case *parse.FieldNode:
		f, _ := compileFieldNode(node, dotType, []parse.Node{node}, nil)
		return func(s state, dot interface{}) interface{} { return f(s, dot, nil) }
	case *parse.PipeNode:
		f, _ := compilePipeline(node, dotType)
		return f
	case *parse.StringNode:
		return func(s state, _ interface{}) interface{} { return node.Text }
	case *parse.IdentifierNode:
		f, _ := compileFunction(node, dotType, nil, nil)
		return func(s state, dot interface{}) interface{} { return f(s, dot, nil) }
	case *parse.VariableNode:
		f, _ := compileVariableNode(node, dotType, nil, nil)
		return func(s state, dot interface{}) interface{} { return f(s, dot, nil) }
	}
	panic(fmt.Errorf("can't handle %s for arg of type %s", node, argType))
}

func compileFunction(node *parse.IdentifierNode, typ reflect.Type, args []parse.Node, final reflect.Type) (cmd command, retType reflect.Type) {
	name := node.Ident
	f, ok := findFunction(name)
	if !ok {
		panic(fmt.Errorf("%q is not a defined function", name))
	}
	lookup := compileFuncCall(typ, f, args[1:], final)
	cmd = func(s state, dot, final interface{}) interface{} {
		v := lookup(s, reflect.ValueOf(dot), final)
		return v.Interface()
	}
	retType = f.Type().Out(0)
	return
}

func findFunction(name string) (reflect.Value, bool) {
	switch name {
	case "print1":
		return reflect.ValueOf(print1), true
	}
	return reflect.Value{}, false
}

func print1(x string) string {
	return x
}

func compileVariableNode(node *parse.VariableNode, dotType reflect.Type, args []parse.Node, finalType reflect.Type) (cmd command, retType reflect.Type) {
	var mu sync.RWMutex
	type key struct {
		dotType, finalType reflect.Type
	}
	cache := make(map[key]command)

	name := node.Ident[0]
	cmd = func(s state, dot, final interface{}) interface{} {
		value := s.varValue(name)
		if len(node.Ident) == 1 {
			return value.Interface()
		}

		if dotType == nil {
			dotType = reflect.ValueOf(dot).Type()
		}
		if finalType == nil && final != nil {
			finalType = reflect.ValueOf(final).Type()
		}
		k := key{dotType, finalType}

		mu.RLock()
		f, exist := cache[k]
		mu.RUnlock()
		if !exist {
			f, _ = compileFieldChain(node.Ident[1:], dotType, args, finalType)
			mu.Lock()
			cache[k] = f
			mu.Unlock()
		}
		return f(s, dot, value)
	}
	return
}
