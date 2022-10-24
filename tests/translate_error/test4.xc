#include <string.xh>

#include <assert.h>

typedef struct foo *foo;

int foo_to_string(foo ignored, char arg2) {
  (void)ignored;
  return 42;
}

show (foo) with foo_to_string; // Wrong type

int main(int argc, char **argv) {
  return 0;
}
