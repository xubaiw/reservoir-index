#include <dlfcn.h>
#include <iostream>

int main(){
  std::cout << "Calling main2" << std::endl;

  void *handle = dlopen("./libplugin2.so", RTLD_LAZY);

  if (!handle) {
    std::cout << "Error Message:" << std::endl << dlerror() << std::endl;
    return 0;
  }

  auto plugin_main = (int (*)())dlsym(handle, "main");

  plugin_main();

  dlclose(handle);
}
