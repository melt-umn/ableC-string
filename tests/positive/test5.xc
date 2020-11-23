#include <string.xh>

#include <assert.h>

typedef struct foo *foo;

string foo_to_string(foo x) {
  return str("Foo!");
}

show foo with foo_to_string;

typedef struct bar {
  foo foo;
} bar;

int main(int argc, char **argv) {
  bar x = (bar) {.foo = NULL};
  assert(show(x) == "{.foo = Foo!}");
  return 0;
}
