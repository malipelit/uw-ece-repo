# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.26

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:

#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:

# Disable VCS-based implicit rules.
% : %,v

# Disable VCS-based implicit rules.
% : RCS/%

# Disable VCS-based implicit rules.
% : RCS/%,v

# Disable VCS-based implicit rules.
% : SCCS/s.%

# Disable VCS-based implicit rules.
% : s.%

.SUFFIXES: .hpux_make_needs_suffix_list

# Command-line flag to silence nested $(MAKE).
$(VERBOSE)MAKESILENT = -s

#Suppress display of executed commands.
$(VERBOSE).SILENT:

# A target that is always out of date.
cmake_force:
.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/local/lib/python3.9/site-packages/cmake/data/bin/cmake

# The command to remove a file.
RM = /usr/local/lib/python3.9/site-packages/cmake/data/bin/cmake -E rm -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/mapelit/ece650-project/mapelit-mrantani

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/mapelit/ece650-project/mapelit-mrantani/build

# Include any dependencies generated for this target.
include CMakeFiles/ece650-prj.dir/depend.make
# Include any dependencies generated by the compiler for this target.
include CMakeFiles/ece650-prj.dir/compiler_depend.make

# Include the progress variables for this target.
include CMakeFiles/ece650-prj.dir/progress.make

# Include the compile flags for this target's objects.
include CMakeFiles/ece650-prj.dir/flags.make

CMakeFiles/ece650-prj.dir/ece650-prj.cpp.o: CMakeFiles/ece650-prj.dir/flags.make
CMakeFiles/ece650-prj.dir/ece650-prj.cpp.o: /home/mapelit/ece650-project/mapelit-mrantani/ece650-prj.cpp
CMakeFiles/ece650-prj.dir/ece650-prj.cpp.o: CMakeFiles/ece650-prj.dir/compiler_depend.ts
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/mapelit/ece650-project/mapelit-mrantani/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object CMakeFiles/ece650-prj.dir/ece650-prj.cpp.o"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -MD -MT CMakeFiles/ece650-prj.dir/ece650-prj.cpp.o -MF CMakeFiles/ece650-prj.dir/ece650-prj.cpp.o.d -o CMakeFiles/ece650-prj.dir/ece650-prj.cpp.o -c /home/mapelit/ece650-project/mapelit-mrantani/ece650-prj.cpp

CMakeFiles/ece650-prj.dir/ece650-prj.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/ece650-prj.dir/ece650-prj.cpp.i"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/mapelit/ece650-project/mapelit-mrantani/ece650-prj.cpp > CMakeFiles/ece650-prj.dir/ece650-prj.cpp.i

CMakeFiles/ece650-prj.dir/ece650-prj.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/ece650-prj.dir/ece650-prj.cpp.s"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/mapelit/ece650-project/mapelit-mrantani/ece650-prj.cpp -o CMakeFiles/ece650-prj.dir/ece650-prj.cpp.s

# Object files for target ece650-prj
ece650__prj_OBJECTS = \
"CMakeFiles/ece650-prj.dir/ece650-prj.cpp.o"

# External object files for target ece650-prj
ece650__prj_EXTERNAL_OBJECTS =

ece650-prj: CMakeFiles/ece650-prj.dir/ece650-prj.cpp.o
ece650-prj: CMakeFiles/ece650-prj.dir/build.make
ece650-prj: minisat/libminisat.a
ece650-prj: /usr/lib/x86_64-linux-gnu/libz.so
ece650-prj: CMakeFiles/ece650-prj.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/mapelit/ece650-project/mapelit-mrantani/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX executable ece650-prj"
	$(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/ece650-prj.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
CMakeFiles/ece650-prj.dir/build: ece650-prj
.PHONY : CMakeFiles/ece650-prj.dir/build

CMakeFiles/ece650-prj.dir/clean:
	$(CMAKE_COMMAND) -P CMakeFiles/ece650-prj.dir/cmake_clean.cmake
.PHONY : CMakeFiles/ece650-prj.dir/clean

CMakeFiles/ece650-prj.dir/depend:
	cd /home/mapelit/ece650-project/mapelit-mrantani/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/mapelit/ece650-project/mapelit-mrantani /home/mapelit/ece650-project/mapelit-mrantani /home/mapelit/ece650-project/mapelit-mrantani/build /home/mapelit/ece650-project/mapelit-mrantani/build /home/mapelit/ece650-project/mapelit-mrantani/build/CMakeFiles/ece650-prj.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : CMakeFiles/ece650-prj.dir/depend

