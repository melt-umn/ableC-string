#include <string.xh>

#include <stdio.h>
#include <stdlib.h>

typedef struct {int a;} t;

int main(int argc, char **argv) {
  string a = str((t){4}); // str of a type without str defined
  string b = 4 * "q";

  b.substring("a");

  char *c = a.text;
  char *d = a; // Implicitly convert string to char*

  a[2] = 'a'; // Assign to string elements
  a.length = 4; // Assign to string length
  a.text = "qwerty"; // Assign to strign text

  return 0;
}
