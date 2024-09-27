#include <string.xh>

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

enum foo {
  A, B, C
};

struct bar {
  enum foo w;
  char *x;
  union {
    int y;
    float z;
  };
};

struct baz {
  struct bar h;
  struct baz *t;
};

allocate_using heap;

int main(int argc, char **argv) {
  string a = str("abc");
  printf("a: %s\n", a.text);

  if (a != "abc")
    return 1;

  if (a == "abcd")
    return 2;
  
  if (a[2] != 'c')
    return 2;

  string b = str("def");
  printf("b: %s\n", b.text);
  string c = "ghi";
  printf("c: %s\n", c.text);
  string d = a + b;
  printf("d: %s\n", d.text);

  if (d != "abcdef")
    return 3;

  d += c;
  d += 'j';
  printf("d: %s\n", d.text);

  if (d != "abcdefghij")
    return 4;

  string e = show(-1234 + 5);
  printf("e: %s\n", e.text);

  if (e != "-1229")
    return 5;
  
  string f = show(-1234) + 5;
  printf("f: %s\n", f.text);

  if (f != "-12345")
    return 6;

  string g = "xyz";
  string h = g * 5;
  printf("h: %s\n", h.text);

  if (h != "xyzxyzxyzxyzxyz")
    return 7;
  
  g *= 7;
  printf("g: %s\n", g.text);

  if (g != "xyzxyzxyzxyzxyzxyzxyz")
    return 8;

  string i = show(3.141592);
  printf("i: %s\n", i.text);

  if (i != "3.14159")
    return 9;

  if (i.length != 7)
    return 10;

  string j = i.substring(3, 6);
  printf("j: %s\n", j.text);
  if (j != "415")
    return 11;

  string k = str("abcd");
  printf("k: %s\n", k.text);
  if (k != "abcd")
    return 12;

  string l = show("abcd");
  printf("l: %s\n", l.text);
  if (l != "\"abcd\"")
    return 13;

  string m = show(show("abcd\n\n\\"));
  printf("m: %s\n", m.text);
  if (m != "\"\\\"abcd\\\\n\\\\n\\\\\\\\\\\"\"")
    return 14;

  int nx = 12;
  int *ny = &nx;
  int *nz = (int *)0x42;
  
  string n = show(ny);
  printf("n: %s\n", n.text);
  if (n != "&12")
    return 15;
  
  string o = str(ny);
  printf("o: %s\n", o.text);
  string p = show(&ny);
  printf("p: %s\n", p.text);
  if (p != "&&12")
    return 16;
  
  string q = str(&ny);
  printf("q: %s\n", q.text);
  string r = show(nz);
  printf("r: %s\n", r.text);
  if (r != "<signed int *  at 0x42>")
    return 17;
  
  string s = str(nz);
  printf("s: %s\n", s.text);

  string t = str(A);
  printf("t: %s\n", t.text);
  if (t != "A")
    return 18;

  string u = show(B);
  printf("u: %s\n", u.text);
  if (u != "B")
    return 19;

  string v = show((enum foo)42);
  printf("v: %s\n", v.text);
  if (v != "<enum foo 42>")
    return 20;

  enum foo foo_C = C;
  string w = show(&foo_C);
  printf("w: %s\n", w.text);
  if (w != "&C")
    return 21;

  const char *strconst = "foobar";
  string x = str(strconst);
  printf("x: %s\n", x.text);
  if (x != "foobar")
    return 22;

  struct baz b1 = {{A, "hello", {.y = 42}}, NULL};
  struct baz b2 = {{B, "world", {.z = 3.14f}}, &b1};
  string y = show(b2);
  printf("y: %s\n", y.text);
  if (y != "{.h = {.w = B, .x = \"world\", {.y = 1078523331, .z = 3.14}}, .t = &{.h = {.w = A, .x = \"hello\", {.y = 42, .z = 5.88545e-44}}, .t = <struct baz *  at (nil)>}}")
    return 23;

  string z = show('\n');
  printf("z: %s\n", z.text);
  if (z != "'\\n'")
    return 24;

  string a1 = str((bool)true);
  printf("a1: %s\n", a1.text);
  if (a1 != "true")
    return 25;

  string c1 = show((bool)false);
  printf("c1: %s\n", c1.text);
  if (c1 != "false")
    return 26;

  string d1 = show(NULL);
  printf("d1: %s\n", d1.text);
  if (d1 != "<void *  at (nil)>")
    return 27;
  
  string e1 = show(main);
  printf("e1: %s\n", e1.text);

  return 0;
}
