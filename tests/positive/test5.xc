#include <string.xh>

#include <assert.h>

typedef struct foo *foo;

size_t foo_max_len(foo ignored) {
  return 4;
}

size_t foo_to_string(char *buf, foo ignored) {
  return sprintf(buf, "Foo!");
}

show foo with foo_max_len, foo_to_string;

allocate_using heap;

typedef struct bar {
  foo foo;
} bar;

int main(int argc, char **argv) {
  bar x = (bar) {.foo = NULL};
  if (show(x) != "{.foo = Foo!}")
    return 1;
  return 0;
}
