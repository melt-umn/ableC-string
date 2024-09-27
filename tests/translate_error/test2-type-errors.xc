#include <string.xh>

#include <stdio.h>
#include <stdlib.h>

typedef struct {int a;} t;

struct foo {
  t *a;
};

allocate_using heap;

int main(int argc, char **argv) {
  string a = str((t){4}); // str of a type without str defined

  t foo = {3};
  string b = show((struct foo){&foo}); // show of a type without show defined
  string c = 4 * "q";

  b.substring("a");

  char *d = a.text;
  char *e = a; // Implicitly convert string to char*

  a[2] = 'a'; // Assign to string elements
  a.length = 4; // Assign to string length
  a.text = "qwerty"; // Assign to string text

  str(1, 3.14); // Wrong number of arguments

  string f = c + foo;
  string g = c + asdfasdf;

  return 0;
}
