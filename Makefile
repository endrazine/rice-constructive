# =============================================================================
# Makefile — A Constructive Proof of Rice's Theorem
#
# Source files (never deleted by any target):
#   rice.tex          — paper (LMCS format, requires lmcs.cls)
#   rice.bib          — bibliography
#   rice.v            — Rocq proof source
#   undecidable.c     — concrete undecidable analysis target (C)
#   lmcs.cls          — LMCS style file (download from lmcs.episciences.org)
#   alphaurl.bst      — BibTeX style for LMCS format
#
# Targets:
#   all               — build everything: PDF, Rocq proof, C program (default)
#   pdf               — build rice.pdf
#   rocq              — verify Rocq proofs with coqc
#   c                 — build undecidable (the concrete C witness)
#   run               — build and run undecidable (both programs)
#   check             — alias for rocq
#   install           — install all dependencies via apt
#   docker            — build Docker image (reproducible environment)
#   docker-run        — build image and extract outputs to ./out/
#   docker-rocq       — run Rocq proof verification inside the container
#   docker-undecidable      — run x^3+y^3+z^3=114 search in background
#   docker-undecidable-log  — follow live output from the search
#   docker-undecidable-stop — stop and remove the search container
#   docker-clean      — remove Docker image and ./out/
#   distclean         — clean + remove .pdf and .vo (never touches source)
#   help              — print this message
#
# Quick start:
#   make install && make all
# =============================================================================

PAPER        = rice
ROCQ         = $(PAPER).v
BIB          = $(PAPER).bib
CLS          = lmcs.cls
C_SRC        = undecidable.c
C_BIN        = undecidable

LATEX        = pdflatex
BIBTEX       = bibtex
LATEXFLAGS   = -interaction=nonstopmode -halt-on-error
CC           = gcc
CFLAGS       = -O2 -Wall -Wextra -Wno-unused-function -std=c11
LDFLAGS      = -lgmp -lm
COQCFLAGS    =

COQC_SNAP    = /snap/bin/coq-prover.coqc
COQC        ?= $(shell \
  if   command -v coqc       >/dev/null 2>&1; then echo coqc; \
  elif [ -x "$(COQC_SNAP)" ];               then echo $(COQC_SNAP); \
  else echo ""; fi)

# =============================================================================

.PHONY: all pdf rocq c run check install docker docker-run docker-rocq docker-clean \
        docker-undecidable docker-undecidable-log docker-undecidable-stop \
        clean distclean watch axioms help \
        _coqc_check _lmcs_check _alphaurl_check

all: pdf rocq c

# --- Docker target ------------------------------------------------------------
#
# Builds a fully reproducible environment and runs the complete build
# inside it: Rocq proof verification + both PDFs + C program.
# Output files are copied to ./out/ on the host.

docker: Dockerfile
	docker build -t rice-constructive .
	@echo ""
	@echo "======================================================="
	@echo "  Docker image built: rice-constructive"
	@echo "  Run: make docker-run   to extract outputs"
	@echo "======================================================="

docker-run: docker
	mkdir -p out
	docker run --rm -v "$(CURDIR)/out:/out" rice-constructive
	@echo ""
	@echo "======================================================="
	@echo "  Outputs written to ./out/"
	@ls -lh out/
	@echo "======================================================="

docker-rocq: docker
	docker run --rm rice-constructive \
	    sh -c 'coqc rice.v && \
	           echo "" && \
	           echo "=======================================================" && \
	           echo "  Rocq: proof verified inside Docker container." && \
	           echo "  Rocq version: $$(coqc --version | head -1)" && \
	           echo "  Axiom: H10C_SAT_undec (coq-library-undecidability)" && \
	           echo "======================================================="'


docker-clean:
	docker rmi -f rice-constructive 2>/dev/null || true
	rm -rf out/
	@echo "Docker image and out/ removed."

docker-undecidable: docker
	@echo ""
	@echo "Starting undecidable search in background container..."
	@echo "Equation: x^3 + y^3 + z^3 = 114 (open problem)"
	@echo ""
	docker run -d --name rice-undecidable rice-constructive \
	    sh -c './undecidable undecidable 2>&1 | tee /undecidable.log'
	@echo "Container started: rice-undecidable"
	@echo ""
	@echo "Useful commands:"
	@echo "  make docker-undecidable-log   — follow live output"
	@echo "  make docker-undecidable-stop  — stop and remove the container"
	@echo "  docker stats rice-undecidable — monitor CPU and memory usage"

docker-undecidable-log:
	docker logs -f rice-undecidable

docker-undecidable-stop:
	docker stop rice-undecidable 2>/dev/null || true
	docker rm   rice-undecidable 2>/dev/null || true
	@echo "Container rice-undecidable stopped and removed."

# --- PDF target ---------------------------------------------------------------

pdf: _lmcs_check _alphaurl_check $(PAPER).pdf
	@echo "======================================================="
	@echo "  PDF: $(PAPER).pdf is up to date."
	@echo "======================================================="

_lmcs_check:
	@if [ ! -f "$(CLS)" ]; then \
	  echo ""; \
	  echo "ERROR: $(CLS) not found."; \
	  echo "Download: https://lmcs.episciences.org/public/lmcs.cls"; \
	  echo "Then place it here and run: make pdf"; \
	  echo ""; \
	  exit 1; \
	fi

_alphaurl_check:
	@if ! kpsewhich alphaurl.bst >/dev/null 2>&1 && [ ! -f alphaurl.bst ]; then \
	  echo ""; \
	  echo "ERROR: alphaurl.bst not found."; \
	  echo "Install: sudo apt install texlive-bibtex-extra"; \
	  echo "Or:      wget https://mirrors.ctan.org/biblio/bibtex/contrib/urlbst/alphaurl.bst"; \
	  echo "Or:      make install"; \
	  echo ""; \
	  exit 1; \
	fi

$(PAPER).pdf: $(PAPER).tex $(BIB) $(CLS)
	$(LATEX) $(LATEXFLAGS) $(PAPER)
	$(BIBTEX) $(PAPER)
	$(LATEX) $(LATEXFLAGS) $(PAPER)
	$(LATEX) $(LATEXFLAGS) $(PAPER)

# --- Rocq target -------------------------------------------------------------

rocq: _coqc_check $(PAPER).vo
	@echo ""
	@echo "======================================================="
	@echo "  Rocq: $(PAPER).vo is up to date — proofs verified."
	@echo "  Axiom: H10C_SAT_undec (coq-library-undecidability)"
	@echo "======================================================="

_coqc_check:
	@if [ -z "$(COQC)" ]; then \
	  echo ""; \
	  echo "ERROR: coqc not found."; \
	  echo "Install: opam install coq   (version 8.20+)"; \
	  echo "Or run:  make install"; \
	  echo ""; \
	  exit 1; \
	fi

$(PAPER).vo: $(ROCQ)
	$(COQC) $(COQCFLAGS) $(ROCQ)
	@echo "  Rocq: proof rebuilt and verified."

# --- C witness program -------------------------------------------------------
#
# undecidable.c is a concrete C program whose termination is provably
# undecidable by static analysis (Theorem Rice_Theorem in rice.v).

c: $(C_BIN)
	@echo "======================================================="
	@echo "  C: $(C_BIN) is up to date."
	@echo "======================================================="

$(C_BIN): $(C_SRC)
	$(CC) $(CFLAGS) $< -o $@ $(LDFLAGS)
	@echo ""
	@echo "======================================================="
	@echo "  Built: $(C_BIN)"
	@echo "  Run: ./$(C_BIN) decidable    (terminates: x^2-y^2-z^2=1)"
	@echo "  Run: ./$(C_BIN) undecidable  (open problem: x^3+y^3+z^3=114)"
	@echo "======================================================="

run: $(C_BIN)
	@echo "=== decidable: x^2 - y^2 - z^2 = 1 (known solvable) ==="
	./$(C_BIN) decidable
	@echo ""
	@echo "=== undecidable: x^3 + y^3 + z^3 = 114 (open problem) ==="
	@echo "    (Ctrl-C to stop — may never terminate)"
	./$(C_BIN) undecidable

# --- Install -----------------------------------------------------------------

install:
	@echo "Installing dependencies..."
	sudo apt-get update -qq
	@echo "Installing Rocq 8.20 via opam + coq-library-undecidability..."
	sudo apt-get install -y opam m4 pkg-config bubblewrap texlive-bibtex-extra gcc libgmp-dev
	opam init --disable-sandboxing -y
	opam switch create rocq-8.20 ocaml-base-compiler.5.2.1
	eval $$(opam env --switch=rocq-8.20) && \
	  opam pin add coq 8.20.0 -n && \
	  opam repo add coq-released https://coq.inria.fr/opam/released && \
	  opam install coq coq-library-undecidability
	@echo ""
	@coqc --version 2>&1 | head -1
	@gcc --version | head -1

# --- Clean -------------------------------------------------------------------
#
# SAFE: never removes source files:
#   *.tex  *.bib  *.v  *.cls  *.bst  *.c  Makefile  README.md

LATEX_AUX = *.aux *.bbl *.blg *.log *.out *.toc *.lof *.lot \
            *.fls *.fdb_latexmk *.synctex.gz
ROCQ_AUX  = *.glob *.vok *.vos

clean:
	@rm -f $(LATEX_AUX) $(ROCQ_AUX) $(C_BIN)
	@echo "Auxiliary files and C binary removed. Source files untouched."

distclean: clean
	@rm -f $(PAPER).pdf $(PAPER).vo
	@echo "Compiled outputs removed. Source files untouched."

# --- Convenience -------------------------------------------------------------

check: rocq

watch:
	@which inotifywait >/dev/null 2>&1 || \
	  (echo "Install: sudo apt install inotify-tools" && exit 1)
	@echo "Watching for changes..."
	@while true; do \
	  inotifywait -q -e modify $(PAPER).tex $(ROCQ) $(BIB) $(C_SRC); \
	  echo "[`date +%H:%M:%S`] Change detected, rebuilding..."; \
	  $(MAKE) all; \
	done

axioms: $(PAPER).vo
	@if command -v coqchk >/dev/null 2>&1; then \
	  coqchk -silent $(PAPER) 2>&1 | grep -A 10 "Axioms:" || true; \
	else \
	  grep "Hypothesis\|Axiom" $(ROCQ); \
	fi

# --- Help --------------------------------------------------------------------

help:
	@echo ""
	@echo "Usage: make [target]"
	@echo ""
	@echo "  all         build PDF, verify Rocq proofs, build C (default)"
	@echo "  pdf         build rice.pdf"
	@echo "  rocq        verify Rocq proofs"
	@echo "  c           build undecidable (concrete C witness)"
	@echo "  run         build and run both programs in undecidable.c"
	@echo "  check       alias for rocq"
	@echo "  install     install dependencies via apt"
	@echo "  axioms      print axioms used by the proof"
	@echo "  docker      build Docker image (fully reproducible)"
	@echo "  docker-run  build image and copy outputs to ./out/"
	@echo "  docker-rocq  run Rocq proof verification inside Docker"
	@echo "  docker-undecidable      run x^3+y^3+z^3=114 search in background"
	@echo "  docker-undecidable-log  follow live output from the search"
	@echo "  docker-undecidable-stop stop and remove the search container"
	@echo "  docker-clean remove Docker image and ./out/"
	@echo "  clean       remove auxiliary files + C binary (SAFE)"
	@echo "  distclean   remove .pdf and .vo too (SAFE)"
	@echo "  watch       rebuild on file changes"
	@echo ""
	@echo "Source files never deleted:"
	@echo "  rice.tex  rice.bib  rice.v  lmcs.cls  undecidable.c  Makefile  README.md"
	@echo ""
	@echo "Status:"
	@if [ -z "$(COQC)" ]; then \
	  echo "  [!] coqc not found                → make install"; \
	else \
	  echo "  [ok] $(shell $(COQC) --version 2>&1 | head -1)"; \
	fi
	@if ! kpsewhich alphaurl.bst >/dev/null 2>&1 && [ ! -f alphaurl.bst ]; then \
	  echo "  [!] alphaurl.bst missing          → make install"; \
	else \
	  echo "  [ok] alphaurl.bst present"; \
	fi
	@if [ ! -f "$(CLS)" ]; then \
	  echo "  [!] lmcs.cls missing              → download from lmcs.episciences.org"; \
	else \
	  echo "  [ok] lmcs.cls present"; \
	fi
	@if command -v gcc >/dev/null 2>&1; then \
	  echo "  [ok] $(shell gcc --version | head -1)"; \
	else \
	  echo "  [!] gcc not found                 → make install"; \
	fi
	@echo ""
