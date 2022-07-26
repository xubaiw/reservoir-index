import Alloy.C
import Curl.Init

open scoped Alloy.C

namespace Curl

alloy c include <curl/curl.h> <lean/lean.h>

alloy c section

static void CURL_finalize(void* ptr) {
  curl_easy_cleanup((CURL*)ptr);
}

static void CURL_foreach(void* ptr, b_lean_obj_arg f) { }

static lean_external_class * g_CURL_class = NULL;

static inline lean_object * CURL_to_lean(CURL* curl) {
  if (g_CURL_class == NULL) {
    g_CURL_class = lean_register_external_class(CURL_finalize, CURL_foreach);
  }
  return lean_alloc_external(g_CURL_class, curl);
}

static inline CURL const * to_CURL(b_lean_obj_arg curl) {
  return (CURL*)(lean_get_external_data(curl));
}

end

opaque Handle.nonempty : NonemptyType
def Handle : Type := Handle.nonempty.type
instance : Nonempty Handle := Handle.nonempty.property

namespace Handle
alloy c extern "lean_curl_easy_handle_mk"
def mk (_u : Unit) : IO Handle := {
  CURL *curl = curl_easy_init();
  if(curl) {
    return lean_io_result_mk_ok(CURL_to_lean(curl));
  }
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("fail to init curl easy handle")));
}

end Handle

end Curl
