#include <string.xh>

#include <assert.h>

typedef struct foo *foo;

size_t foo_max_len(foo ignored) {
  return 30;
}

int foo_to_string(foo ignored, char arg2) {
  (void)ignored;
  return 42;
}

show (foo) with foo_max_len, foo_to_string; // Wrong type

int main(int argc, char **argv) {
  return 0;
}
