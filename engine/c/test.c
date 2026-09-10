#include <stdio.h>
#include <string.h>
int mathengine_init(void); char* mathengine_call(const char*); void mathengine_free(char*);
int main(void) {
  if (mathengine_init()) return 1;
  const char* reqs[] = {
    "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"engine.capabilities\",\"params\":{}}",
    "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"engine.evaluate\",\"params\":{\"sessionId\":\"s\",\"cellId\":\"c\",\"source\":\"(x*1 + 0) * 1\"}}",
    "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"engine.evaluate\",\"params\":{\"sessionId\":\"s\",\"cellId\":\"f\",\"source\":\"let f = x^2\"}}",
    "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"engine.evaluate\",\"params\":{\"sessionId\":\"s\",\"cellId\":\"d\",\"source\":\"diff(f, x)\"}}",
  };
  for (int i = 0; i < 4; i++) {
    for (int rep = 0; rep < 500; rep++) {            /* 2000 calls: leaks/refcount bugs show up here */
      char* r = mathengine_call(reqs[i]);
      if (rep == 0) puts(r);
      mathengine_free(r);
    }
  }
  puts("ABI-OK");
  return 0;
}
