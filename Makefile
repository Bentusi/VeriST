# IEC 61131-3 ST Compiler in Coq - Makefile

# Coq configuration
COQMAKEFILE := Makefile.coq
COQ_PROJ := _CoqProject

# OCaml extraction directory
EXTRACT_DIR := extraction
EXTRACT_BUILD := $(EXTRACT_DIR)/_build

# Targets
.PHONY: all clean cleanall theories extract test install

# Default target
all: theories

# Build Coq theories
theories: $(COQMAKEFILE)
	@echo "==> Building Coq theories..."
	$(MAKE) -f $(COQMAKEFILE)

# Generate Makefile.coq from _CoqProject
$(COQMAKEFILE): $(COQ_PROJ)
	@echo "==> Generating Makefile.coq..."
	coq_makefile -f $(COQ_PROJ) -o $(COQMAKEFILE)

# Extract OCaml code
extract: theories
	@echo "==> Extracting OCaml code..."
	@mkdir -p $(EXTRACT_DIR)
	coqc theories/Extraction/Extract.v
	@echo "==> OCaml code extracted to $(EXTRACT_DIR)/"

# Build extracted OCaml code
build-extract: extract
	@echo "==> Building extracted OCaml code..."
	cd $(EXTRACT_DIR) && dune build

# Run tests
test: theories
	@echo "==> Running tests..."
	@for file in examples/*.v; do \
		echo "Testing $$file..."; \
		coqc -R theories STCompiler $$file || exit 1; \
	done
	@echo "==> All tests passed!"

# Install (optional)
install: theories
	$(MAKE) -f $(COQMAKEFILE) install

# Clean build artifacts
clean:
	@echo "==> Cleaning build artifacts..."
	@if [ -f $(COQMAKEFILE) ]; then $(MAKE) -f $(COQMAKEFILE) clean; fi
	@rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf
	@find . -name "*.vo" -o -name "*.vok" -o -name "*.vos" -o -name "*.glob" -o -name ".*.aux" | xargs rm -f
	@rm -rf $(EXTRACT_BUILD)
	@echo "==> Cleaning OCaml extraction artifacts..."
	@rm -f *.ml *.mli *.cmo *.cmi *.cmx *.o *.cmt *.cmti
	@if [ -d $(EXTRACT_DIR) ]; then cd $(EXTRACT_DIR) && $(MAKE) clean 2>/dev/null || true; fi
	@echo "==> Clean complete!"

# Deep clean - remove all generated files including extracted sources
cleanall: clean
	@echo "==> Deep cleaning (removing extracted sources)..."
	@rm -f *.ml *.mli
	@if [ -d $(EXTRACT_DIR) ]; then cd $(EXTRACT_DIR) && $(MAKE) cleanall 2>/dev/null || true; fi
	@echo "==> Deep clean complete!"

# Help
help:
	@echo "IEC 61131-3 ST Compiler - Makefile targets:"
	@echo "  all           - Build all Coq theories (default)"
	@echo "  theories      - Build Coq theories"
	@echo "  extract       - Extract OCaml code from Coq"
	@echo "  build-extract - Build the extracted OCaml code"
	@echo "  test          - Run test examples"
	@echo "  clean         - Clean build artifacts (keep sources)"
	@echo "  cleanall      - Deep clean (remove extracted sources too)"
	@echo "  install       - Install the library"
	@echo "  help          - Show this help message"
