CXX ?= g++
CXXFLAGS ?= -g -std=c++17 -Wall -Wextra -Wconversion -pedantic -O2
INCLUDES := -Iinclude

SRC_DIR := src
AST_SRC := $(SRC_DIR)/ast
CFIR_SRC := $(SRC_DIR)/cfir

INC_DIR := include
AST_INC := $(INC_DIR)/ast
CFIR_INC := $(INC_DIR)/cfir

BUILD_DIR := bin

SRC_FILES := $(wildcard $(SRC_DIR)/*.cpp)
OBJ_FILES := $(patsubst $(SRC_DIR)/%.cpp, $(BUILD_DIR)/%.o, $(SRC_FILES))

AST_SRC_FILES := $(wildcard $(AST_SRC)/*.cpp)
AST_OBJ_FILES := $(patsubst $(AST_SRC)/%.cpp, $(BUILD_DIR)/ast/%.o, $(AST_SRC_FILES))

CFIR_SRC_FILES := $(wildcard $(CFIR_SRC)/*.cpp)
CFIR_OBJ_FILES := $(patsubst $(CFIR_SRC)/%.cpp, $(BUILD_DIR)/cfir/%.o, $(CFIR_SRC_FILES))

OBJECTS := $(OBJ_FILES) $(AST_OBJ_FILES) $(CFIR_OBJ_FILES)


$(BUILD_DIR)/%.o: $(SRC_DIR)/%.cpp $(INC_DIR)/%.h
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) $(INCLUDES) $< -c -o $@

$(BUILD_DIR)/ast/%.o: $(AST_SRC)/%.cpp $(AST_INC)/%.h
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) $(INCLUDES) $< -c -o $@

$(BUILD_DIR)/cfir/%.o: $(CFIR_SRC)/%.cpp $(CFIR_INC)/%.h
	@mkdir -p $(@D)
	$(CXX) $(CXXFLAGS) $(INCLUDES) $< -c -o $@

all: main.out MergeTool.o

main.out: $(OBJECTS) main.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) $^ -o $@

MergeTool.o: $(OBJECTS) MergeTool.cpp
	$(CXX) $(CXXFLAGS) $(INCLUDES) $^ -o $@

.PHONY: clean
clean:
	rm -rf main.out MergeTool.o $(BUILD_DIR)