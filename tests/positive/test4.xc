#include <string.xh>

#include <assert.h>

typedef struct foo { int x; } *foo;

size_t struct_foo_max_len(struct foo ignored) {
  return 20;
}

size_t struct_foo_to_string(char *buf, struct foo x) {
  return sprintf(buf, "struct foo: %d", x.x);
}

size_t foo_max_len(foo ignored) {
  return 30;
}

size_t foo_to_string(char *buf, foo x) {
  return sprintf(buf, "pointer to struct foo: %d", x->x);
}

show foo with foo_max_len, foo_to_string;
show struct foo with struct_foo_max_len, struct_foo_to_string;

allocate_using heap;

int main(int argc, char **argv) {
  foo x = malloc(sizeof(struct foo));
  x->x = 42;
  if (show(x) != "pointer to struct foo: 42")
    return 1;
  if (show(*x) != "struct foo: 42")
    return 2;
  return 0;
}
