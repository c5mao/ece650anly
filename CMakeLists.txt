cmake_minimum_required(VERSION 2.8)
project(anly-ece650)

if (EXISTS "${CMAKE_SOURCE_DIR}/minisat")
  add_subdirectory(minisat)
else()
  message (FATAL_ERROR "MiniSat not found. Use `git clone https://github.com/agurfinkel/minisat` to check it out.")
endif()


## ECE650 Specific configuration start here
## Project specific configurations go here

# enable c++11 support
set (CMAKE_CXX_FLAGS "-std=gnu++11 -Wall -lrt ${CMAKE_CXX_FLAGS}")

# expose minisat header files
include_directories(${CMAKE_SOURCE_DIR}/minisat)

# create the main executable
## add additional .cpp files if needed
add_executable(anly-ece650 anly-ece650.cpp)
# link MiniSAT libraries
target_link_libraries(anly-ece650 minisat-lib-static)
# link pthread libraries
target_link_libraries(anly-ece650 pthread)

