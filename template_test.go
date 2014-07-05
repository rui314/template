package template

import (
	"bytes"
	"io"
	"strings"
	"testing"
	std "text/template"
)

var _ = strings.Repeat

func TestNew(t *testing.T) {
	tmpl := New()
	if tmpl == nil {
		t.Error("template expected; got nil")
	}
}

func TestParse(t *testing.T) {
	tmpl, err := New().Parse("")
	if err != nil {
		t.Errorf("got %v", err)
	}
	if tmpl == nil {
		t.Error("template expected; got nil")
	}
}

type T1 struct {
	X T2
}

type T2 struct {
	Y string
}

func (v T2) M1() string {
	return "<" + v.Y + ">"
}

func (v T2) M2(s string) string {
	return "<" + s + ">"
}

type testCase struct {
	input  string
	output string
	dot    interface{}
}

var testCases = []testCase{
	{"x", "x", ""},
	{"{{3}}", "3", ""},
	{"{{true}}", "true", ""},
	{"{{false}}", "false", ""},
	{"{{.}}", "abc", "abc"},
	{"{{.}}", "123", 123},
	{"{{.M1}}", "<foo>", T2{"foo"}},
	{"{{.X.Y}}", "foo", T1{T2{"foo"}}},
	{"{{.X.M1}}", "<foo>", T1{T2{"foo"}}},
	{"{{.X}}", "xyz", map[string]string{"X": "xyz"}},

	{"{{if true}}x{{end}}", "x", ""},
	{"{{if true}}x{{else}}y{{end}}", "x", ""},
	{"{{if 1}}x{{else}}y{{end}}", "x", ""},
	{"{{if 1.0}}x{{else}}y{{end}}", "x", ""},
	{`{{if "foo"}}x{{else}}y{{end}}`, "x", ""},
	{`{{if .}}x{{else}}y{{end}}`, "x", true},
	{`{{if .}}x{{else}}y{{end}}`, "x", 1},
	{`{{if .}}x{{else}}y{{end}}`, "x", T2{"foo"}},

	{"{{if false}}x{{end}}", "", ""},
	{"{{if false}}x{{else}}y{{end}}", "y", ""},
	{"{{if 0}}x{{else}}y{{end}}", "y", ""},
	{"{{if 0.0}}x{{else}}y{{end}}", "y", ""},
	{`{{if ""}}x{{else}}y{{end}}`, "y", ""},
	{`{{if .}}x{{else}}y{{end}}`, "y", false},
	{`{{if .}}x{{else}}y{{end}}`, "y", 0},

	{"{{with true}}{{.}}{{end}}", "true", ""},
	{"{{with false}}{{.}}{{end}}", "", ""},

	{"{{with .X}}{{.Y}}{{end}}", "foo", T1{T2{"foo"}}},

	{"{{.X}}", "foo", struct{ X interface{} }{"foo"}},
	{"{{.X.Y}}", "foo", struct{ X interface{} }{interface{}(struct{ Y string }{"foo"})}},

	{`{{(.M2 "x")}}`, "<x>", T2{}},
	{`{{("x"|.M2)}}`, "<x>", T2{}},
	{`{{("xyz"|print1)}}`, "xyz", ""},

	{"{{$}}", "3", 3},
	{"{{$.X}}", "abc", map[string]string{"X": "abc"}},
	{"{{$x:=3}}{{$x}}", "3", ""},
}

func TestExecute(t *testing.T) {
	for i, tc := range testCases {
		tmpl := Must(New().Parse(tc.input))
		buf := &bytes.Buffer{}
		err := tmpl.Execute(buf, tc.dot)
		if err != nil {
			t.Errorf("execute: %s", err)
		}
		if got := buf.String(); got != tc.output {
			t.Errorf(`%d: execute: expected %q, got %q`, i, tc.input, got)
		}
	}
}

const letter = `Dear {{.Name}},
{{if .Attended}}It was a pleasure to see you at the wedding.{{else}}
It is a shame you couldn't make it to the wedding.{{end}}
{{with .Gift}}Thank you for the lovely {{.}}.
{{end}}Best wishes,
Josie`

type Recipient struct {
	Name     string
	Gift     string
	Attended bool
}

var recipients = []Recipient{
	{"Aunt Mildred", "bone china tea set", true},
	{"Uncle John", "moleskin pants", false},
	{"Cousin Rodney", "", false},
}

func TestLetter(t *testing.T) {
	tmpl := Must(New().Parse(letter))
	buf := &bytes.Buffer{}
	err := tmpl.Execute(buf, recipients[0])
	if err != nil {
		t.Error("executing template:", err)
	}
	expect := `Dear Aunt Mildred,
It was a pleasure to see you at the wedding.
Thank you for the lovely bone china tea set.
Best wishes,
Josie`
	if got := buf.String(); got != expect {
		t.Errorf("expect %q, got %q", expect, got)
	}
}

func benchmark(b *testing.B, f func(io.Writer, interface{}) error) {
	buf := &bytes.Buffer{}
	var l int
	for i := 0; i < b.N; i++ {
		l = 0
		for _, r := range recipients {
			err := f(buf, r)
			if err != nil {
				b.Fatal("executing template:", err)
			}
			l += buf.Len()
			buf.Reset()
		}
	}
	b.SetBytes(int64(l))
}

func BenchmarkMyExecute(b *testing.B) {
	tmpl := Must(New().Parse(letter))
	benchmark(b, tmpl.Execute)
}

func BenchmarkStdExecute(b *testing.B) {
	tmpl := std.Must(std.New("letter").Parse(letter))
	benchmark(b, tmpl.Execute)
}
