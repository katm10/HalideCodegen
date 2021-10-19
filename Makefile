CXX ?= g++
CXXFLAGS ?= -g -std=c++17 -Wno-attributes -O2 -I ../Halide/include/ -L ../Halide/bin/ -lHalide
INCLUDES := -Iinclude

SRC_DIR := src
INC_DIR := include
BUILD_DIR := bin

SRC_FILES := $(wildcard $(SRC_DIR)/*.cpp)
OBJ_FILES := $(patsubst $(SRC_DIR)/%.cpp, $(BUILD_DIR)/%.o, $(SRC_FILES))

$(BUILD_DIR)/%.o: $(SRC_DIR)/%.cpp $(INC_DIR)/%.h
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) $(INCLUDES) $< -c -o $@

main.out: $(OBJ_FILES) main.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) $^ -o $@ -lHalide

MergeTool.o: $(OBJ_FILES) MergeTool.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) $^ -o $@

.PHONY: clean
clean:
	rm -rf main.out $(BUILD_DIR)