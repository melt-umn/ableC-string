#include <string.xh>

#include <assert.h>

typedef struct foo { int x; } *foo;

string struct_foo_to_string(struct foo x) {
  return str("struct foo: ") + show(x.x);
}

string foo_to_string(foo x) {
  return str("pointer to struct foo: ") + show(x->x);
}

show foo with foo_to_string;
show struct foo with struct_foo_to_string;

int main(int argc, char **argv) {
  foo x = malloc(sizeof(struct foo));
  x->x = 42;
  assert(show(x) == "pointer to struct foo: 42");
  assert(show(*x) == "struct foo: 42");
  return 0;
}
