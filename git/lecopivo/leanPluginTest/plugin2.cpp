#include <dlfcn.h>

#include <iostream>

#include <lean/lean.h>

extern "C" void lean_initialize_runtime_module();

int main() {
  std::cout << "Calling Plugin main" << std::endl;

  while(1){

    void *handle = dlopen("../lib/Package.so", RTLD_LAZY);
    
    if (!handle) {
      std::cout << "Error Message:" << std::endl << dlerror() << std::endl;
      return 0;
    }
    
    auto initialize_Package = (lean_object* (*)(lean_object*))dlsym(handle, "initialize_Package");
    auto _lean_main = (lean_object* (*)(lean_object*))dlsym(handle, "_lean_main");
    
    if (!initialize_Package || !_lean_main) {
      std::cout << "Error Message:" << std::endl << dlerror() << std::endl;
      return 0;
    }
    
    lean_object* res;
    lean_initialize_runtime_module();
    lean_set_panic_messages(false);
    res = initialize_Package(lean_io_mk_world());
    lean_set_panic_messages(true);
    lean_io_mark_end_initialization();
    if (lean_io_result_is_ok(res)) {
      lean_dec_ref(res);
      lean_init_task_manager();
      res = _lean_main(lean_io_mk_world());
    }
    lean_finalize_task_manager();
    if (lean_io_result_is_ok(res)) {
      int ret = 0;
      lean_dec_ref(res);
    } else {
      lean_io_result_show_error(res);
      lean_dec_ref(res);
    }
    
    dlclose(handle);
  }
}



  
