#!/bin/bash

# Build script for VeriST OCaml extraction

echo "=== Building VeriST Compiler ==="

# Compile all .mli files first
echo "Compiling interfaces..."
ocamlc -c Datatypes.mli BinNums.mli BinPos.mli BinInt.mli \
  Zbool.mli QArith_base.mli Ascii.mli String.mli List.mli \
  Types.mli Values.mli Environment.mli AST.mli Bytecode.mli \
  Operations.mli VM.mli VMSemantics.mli CompilerState.mli Compiler.mli

# Compile all .ml files
echo "Compiling implementations..."
ocamlc -c Datatypes.ml BinNums.ml BinPos.ml BinInt.ml \
  Zbool.ml QArith_base.ml Ascii.ml String.ml List.ml \
  Types.ml Values.ml Environment.ml AST.ml Bytecode.ml \
  Operations.ml VM.ml VMSemantics.ml CompilerState.ml Compiler.ml main.ml

# Link everything
echo "Linking..."
ocamlc -o veriST \
  Datatypes.cmo BinNums.cmo BinPos.cmo BinInt.cmo \
  Zbool.cmo QArith_base.cmo Ascii.cmo String.cmo List.cmo \
  Types.cmo Values.cmo Environment.cmo AST.cmo Bytecode.cmo \
  Operations.cmo VM.cmo VMSemantics.cmo CompilerState.cmo \
  Compiler.cmo main.cmo

echo "=== Build complete! ==="
echo "Run ./veriST to test the compiler"
