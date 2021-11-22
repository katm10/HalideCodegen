CXX ?= g++
CXXFLAGS ?= -g -std=c++17 -Wno-attributes -O2 -I ../Halide/include/ -L ../Halide/bin/ -lHalide
INCLUDES := -Iinclude -Ihalide-include

SRC_DIR := src
INC_DIR := include
HALIDE_INC_DIR := halide-include
BUILD_DIR := bin

SRC_FILES := $(wildcard $(SRC_DIR)/*.cpp)
OBJ_FILES := $(patsubst $(SRC_DIR)/%.cpp, $(BUILD_DIR)/%.o, $(SRC_FILES))

$(BUILD_DIR)/%.o: $(SRC_DIR)/%.cpp $(INC_DIR)/%.h
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) $(INCLUDES) $< -c -o $@

$(BUILD_DIR)/%.o: $(SRC_DIR)/%.cpp $(HALIDE_INC_DIR)/%.h
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) $(INCLUDES) $< -c -o $@

all: main.out MergeTool.o

main.out: $(OBJ_FILES) main.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) $^ -o $@ -lHalide

MergeTool.o: $(OBJ_FILES) MergeTool.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) $^ -o $@ -lHalide

.PHONY: clean
clean:
	rm -rf main.out MergeTool.o $(BUILD_DIR)