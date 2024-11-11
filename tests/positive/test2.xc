#include <string.xh>
#include <stdio.h>
#include <stdlib.h>

struct foo {
  int x;
  float y;
  string z;
};

int main() {
  struct foo thing = {1, 2.34, "abc"};

  char buf[showMaxLen(thing) + 7];
  size_t len = buildStr(buf, show(thing) + " " + (str("!") * 3) + " " + str(42));
  printf("%zu\n", len);
  printf("%s\n", buf);

  if (len != strlen(buf))
    return 1;

  if (strcmp(buf, "{.x = 1, .y = 2.34, .z = \"abc\"} !!! 42"))
    return 2;
}
