#include <dlfcn.h>

#include <iostream>

#include <lean/lean.h>

int main() {
  std::cout << "Calling Plugin main" << std::endl;

  while(1){

    void *handle = dlopen("../lib/Package.so", RTLD_LAZY);
    
    if (!handle) {
      std::cout << "Error Message:" << std::endl << dlerror() << std::endl;
      return 0;
    }
    
  // auto package_main = (int (*)(int argc, char ** argv))dlsym(handle, "main");
    auto lean_initialize_runtime_module = (void (*)())dlsym(handle, "lean_initialize_runtime_module");
    auto initialize_Package = (lean_object* (*)(lean_object*))dlsym(handle, "initialize_Package");
    auto _lean_main = (lean_object* (*)(lean_object*))dlsym(handle, "_lean_main");
    auto lean_dec_ref_cold = (void (*)(lean_object*))dlsym(handle, "lean_dec_ref_cold");
    auto lean_io_mark_end_initialization = (void (*)())dlsym(handle, "lean_io_mark_end_initialization");
    auto lean_init_task_manager = (void (*)())dlsym(handle, "lean_init_task_manager");
    auto lean_finalize_task_manager = (void (*)())dlsym(handle, "lean_finalize_task_manager");
    
    auto lean_dec_ref = [&](lean_object * o) {
      if (LEAN_LIKELY(o->m_rc > 1)) {
        o->m_rc--;
      } else if (o->m_rc != 0) {
        lean_dec_ref_cold(o);
      }
    };
    
    auto package_main = (int (*)(int, char **))dlsym(handle, "main");
    
    if (!lean_initialize_runtime_module ||
	!initialize_Package ||
	!_lean_main ||
	!lean_dec_ref_cold ||
	!lean_io_mark_end_initialization ||
	!lean_init_task_manager) {
      std::cout << "Error Message:" << std::endl << dlerror() << std::endl;
      return 0;
    }
    
    lean_object* res;
    lean_initialize_runtime_module();
    res = initialize_Package(lean_io_mk_world());
    lean_io_mark_end_initialization();
    if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
      lean_init_task_manager();
      res = _lean_main(lean_io_mk_world());
    }
    lean_finalize_task_manager();
    if (lean_io_result_is_ok(res)) {
      lean_dec_ref(res);
    } else {
      lean_dec_ref(res);
    }
    
    dlclose(handle);
  }
}



  
