#include <string.xh>
#include <stdio.h>
#include <stdlib.h>

struct foo {
  int x;
  float y;
  string z;
};

int test_show_no_alloc(struct foo thing) {
  size_t maxLen = showMaxLen(thing);
  printf("%zu\n", maxLen);
  if (maxLen != 72)
    return 2;

  char buf[maxLen + 1];
  size_t len = showToBuf(buf, thing);
  printf("%zu\n", len);
  printf("%s\n", buf);
  if (len != 31)
    return 3;

  if (strcmp(buf, "{.x = 1, .y = 2.34, .z = \"abc\"}"))
    return 4;

  return 0;
}

int main() {
  allocate_using heap;
  struct foo thing = {1, 2.34, "abc"};

  string res = show(thing);
  printf("%s\n", res.text);
  if (res != "{.x = 1, .y = 2.34, .z = \"abc\"}")
    return 1;

  return test_show_no_alloc(thing);
}