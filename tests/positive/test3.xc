#include <string.xh>

#include <assert.h>

typedef struct foo *foo;

string foo_to_string(foo ignored) {
  (void)ignored;
  return str("Foo!");
}

show (foo) with foo_to_string;

int main(int argc, char **argv) {
  foo x = NULL;
  assert(show(x) == "Foo!");
  return 0;
}
