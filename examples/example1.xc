#include <string.xh>

#include <stdio.h>
#include <stdlib.h>

enum foo {
  A, B, C
};

int main(int argc, char **argv) {
  string a;
  a = "abc";
  printf("a: %s\n", a.text);

  if (a != "abc")
    return 1;

  if (a == "abcd")
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

  int x = 12;
  int *y = &x;
  int *z = (int *)0x42;
  
  string n = show(y);
  printf("n: %s\n", n.text);
  string o = str(y);
  printf("o: %s\n", o.text);
  string p = show(&y);
  printf("p: %s\n", p.text);
  string q = str(&y);
  printf("q: %s\n", q.text);
  string r = show(z);
  printf("r: %s\n", r.text);
  string s = str(z);
  printf("s: %s\n", s.text);

  string t = str(A);
  printf("t: %s\n", t.text);
  string u = show(B);
  printf("u: %s\n", u.text);
  string v = show((enum foo)42);
  printf("v: %s\n", v.text);

  enum foo foo_C = C;
  string w = show(&foo_C);
  printf("w: %s\n", w.text);
  
  return 0;
}
