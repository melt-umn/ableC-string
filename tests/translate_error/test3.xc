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
show foo with foo_max_len, foo_to_string; // Duplicate!

allocate_using heap;

int main(int argc, char **argv) {
  foo x = NULL;
  assert(show(x) == "Foo!");
  return 0;
}
