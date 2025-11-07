#!/bin/bash

# Build VeriST Compiler with Parser

set -e  # Exit on error

echo "=== Building VeriST Compiler ==="
echo ""

# Step 1: Generate lexer and parser
echo "[1/4] Generating lexer and parser..."
ocamllex lexer.mll
ocamlyacc parser.mly

# Step 2: Compile all extracted Coq modules
echo "[2/4] Compiling Coq-extracted modules..."
ocamlc -c Datatypes.mli Datatypes.ml
ocamlc -c BinNums.mli BinNums.ml
ocamlc -c BinPos.mli BinPos.ml
ocamlc -c BinInt.mli BinInt.ml
ocamlc -c Ascii.mli Ascii.ml
ocamlc -c String.mli String.ml
ocamlc -c List.mli List.ml
ocamlc -c QArith_base.mli QArith_base.ml
ocamlc -c Zbool.mli Zbool.ml
ocamlc -c Types.mli Types.ml
ocamlc -c Values.mli Values.ml
ocamlc -c AST.mli AST.ml
ocamlc -c Environment.mli Environment.ml
ocamlc -c Operations.mli Operations.ml
ocamlc -c Bytecode.mli Bytecode.ml
ocamlc -c CompilerState.mli CompilerState.ml
ocamlc -c Compiler.mli Compiler.ml
ocamlc -c VMSemantics.mli VMSemantics.ml
ocamlc -c VM.mli VM.ml

# Step 3: Compile parser and lexer
echo "[3/4] Compiling parser and lexer..."
ocamlc -c parser.mli parser.ml
ocamlc -c lexer.ml

# Step 3.5: Compile bytecode builder
echo "[3.5/4] Compiling bytecode builder..."
ocamlc -c bytecode_builder.ml

# Step 4: Compile and link main compiler
echo "[4/4] Linking compiler executable..."
ocamlc -c veriST.ml
ocamlc -o veriST \
  Datatypes.cmo BinNums.cmo BinPos.cmo BinInt.cmo Zbool.cmo \
  Ascii.cmo String.cmo List.cmo QArith_base.cmo \
  Types.cmo Values.cmo AST.cmo Environment.cmo Operations.cmo \
  Bytecode.cmo CompilerState.cmo Compiler.cmo VMSemantics.cmo VM.cmo \
  parser.cmo lexer.cmo bytecode_builder.cmo veriST.cmo

echo ""
echo "✓ Compiler built successfully!"
echo ""
echo "Usage: ./veriST -c <input.st> -o <output.stbc>"
echo "Example: ./veriST -c test_factorial.st -o factorial.stbc"
