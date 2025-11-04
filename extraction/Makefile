# OCaml Makefile for extracted VeriST compiler

# OCaml compiler
OCAMLC = ocamlc
OCAMLOPT = ocamlopt

# Source files (in dependency order)
SOURCES = \
	Datatypes.ml \
	BinNums.ml \
	BinPos.ml \
	BinInt.ml \
	Zbool.ml \
	QArith_base.ml \
	Ascii.ml \
	String.ml \
	List.ml \
	Types.ml \
	Values.ml \
	Environment.ml \
	AST.ml \
	Bytecode.ml \
	Operations.ml \
	VM.ml \
	VMSemantics.ml \
	CompilerState.ml \
	Compiler.ml \
	main.ml

# Object files
OBJS = $(SOURCES:.ml=.cmo)
OPTOBJS = $(SOURCES:.ml=.cmx)

# Output executable
TARGET = veriST
OPTTARGET = veriST.opt

# Build rules
all: bytecode

bytecode: $(TARGET)

native: $(OPTTARGET)

$(TARGET): $(OBJS)
	$(OCAMLC) -o $@ nums.cma $(OBJS)

$(OPTTARGET): $(OPTOBJS)
	$(OCAMLOPT) -o $@ nums.cmxa $(OPTOBJS)

%.cmi: %.mli
	$(OCAMLC) -c $<

%.cmo: %.ml %.cmi
	$(OCAMLC) -c $<

%.cmx: %.ml %.cmi
	$(OCAMLOPT) -c $<

# For main.ml which doesn't have .mli
main.cmo: main.ml
	$(OCAMLC) -c $<

main.cmx: main.ml
	$(OCAMLOPT) -c $<

.PHONY: clean test

clean:
	rm -f *.cmo *.cmi *.cmx *.o $(TARGET) $(OPTTARGET)

test: $(TARGET)
	./$(TARGET)

.DEFAULT_GOAL := all
