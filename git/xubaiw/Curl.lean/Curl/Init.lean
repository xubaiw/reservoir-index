import Alloy.C
open scoped Alloy.C

namespace Curl

alloy c include <stdlib.h> <curl/curl.h> <lean/lean.h>

alloy c extern "lean_curl_initialize"
def init (_u : Unit) : IO Unit := {
  curl_global_init(CURL_GLOBAL_DEFAULT);
  atexit(curl_global_cleanup);
  return lean_io_result_mk_ok(lean_box(0));
}

builtin_initialize init ()

end Curl
