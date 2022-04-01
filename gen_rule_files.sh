#!/usr/bin/env bash

RULE_FILES="rules/Simplify*.rewrites"
GEN_FOLDER="generated/fold_change/"

make MergeTool.o

rm -rf $GEN_FOLDER
mkdir $GEN_FOLDER

for f in $RULE_FILES
do
  echo "Processing $f..."
  ./MergeTool.o $f > $GEN_FOLDER$(basename $f .rewrites)_Helper.cpp
  CODE=$?
  if [[ $CODE -ne 0 ]]; then
    echo "Error in $(basename $f) (exit code $CODE)"
    mv $GEN_FOLDER$(basename $f .rewrites)_Helper.cpp $GEN_FOLDER$(basename $f .rewrites)-ERROR.out
  fi
done