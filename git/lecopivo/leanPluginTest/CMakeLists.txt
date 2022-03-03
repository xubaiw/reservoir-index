project(LeanPluginTest)
cmake_minimum_required(VERSION 3.10)

add_executable(main main.cpp)
target_link_libraries(main dl)

add_library(plugin SHARED plugin.cpp)
target_include_directories(plugin PUBLIC "~/.elan/toolchains/leanprover--lean4---nightly/include")


add_executable(main2 main2.cpp)
target_link_libraries(main2 dl)

add_library(plugin2 SHARED plugin2.cpp)
target_include_directories(plugin2 PUBLIC "~/.elan/toolchains/leanprover--lean4---nightly/include")

target_link_directories(plugin2 PUBLIC "~/.elan/toolchains/leanprover--lean4---nightly/lib/lean")
target_link_libraries(plugin2 leanshared)

