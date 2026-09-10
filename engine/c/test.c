#include <stdio.h>
#include <string.h>
int mathengine_init(void); char* mathengine_call(const char*); void mathengine_free(char*);
int main(void) {
  if (mathengine_init()) return 1;
  const char* reqs[] = {
    "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"engine.capabilities\",\"params\":{}}",
    "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"engine.evaluate\",\"params\":{\"source\":\"(x*1 + 0) * 1\"}}",
  };
  for (int i = 0; i < 2; i++) {
    for (int rep = 0; rep < 1000; rep++) {           /* 1000 calls: leaks/refcount bugs show up here */
      char* r = mathengine_call(reqs[i]);
      if (rep == 0) puts(r);
      mathengine_free(r);
    }
  }
  puts("ABI-OK");
  return 0;
}
