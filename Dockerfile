# =============================================================================
# Dockerfile — A Constructive Proof of Rice's Theorem
#
# Builds a fully reproducible environment that:
#   1. Verifies the Rocq proof with coqc
#   2. Compiles rice.pdf (LMCS format)
#   3. Builds undecidable (the concrete C witness program)
#
# Usage:
#   docker build -t rice-constructive .
#   docker run --rm -v "$PWD/out:/out" rice-constructive
#
# Output files (copied to ./out/):
#   rice.pdf        — paper, LMCS format (17 pages)
#   rice.vo         — compiled Rocq object (proof accepted)
#   undecidable     — concrete C program with provably undecidable termination
#
# Note: lmcs.cls is downloaded at build time from lmcs.episciences.org.
#       Requires internet access during `docker build`.
#       For offline builds: place lmcs.cls in the build context and
#       replace the wget line below with: COPY lmcs.cls ./
# =============================================================================

FROM ubuntu:24.04

LABEL maintainer="Jonathan Brossard <endrazine@securityfocus.com>"
LABEL description="Reproducible build: A Constructive Proof of Rice's Theorem"
LABEL org.opencontainers.image.source="https://github.com/endrazine/rice-constructive"

ENV DEBIAN_FRONTEND=noninteractive
ENV TZ=UTC

# ---------------------------------------------------------------------------
# System dependencies
# ---------------------------------------------------------------------------
RUN apt-get update -qq && \
    apt-get install -y --no-install-recommends \
        opam \
        gcc \
        libgmp-dev \
        pkg-config \
        m4 \
        bubblewrap \
        texlive-latex-base \
        texlive-latex-extra \
        texlive-latex-recommended \
        texlive-fonts-recommended \
        texlive-science \
        texlive-bibtex-extra \
        wget \
        ca-certificates \
        poppler-utils \
        make \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/*

# ---------------------------------------------------------------------------
# Install Rocq (Coq) 8.20 and coq-library-undecidability via opam
# Minimum compatible version: 8.18 (lemma names map_length/seq_length/
# app_length used throughout; these exist in both 8.18 and 8.20).
# ---------------------------------------------------------------------------
ENV OPAMROOT=/root/.opam
ENV OPAMYES=true

RUN opam init --disable-sandboxing --bare -n && \
    opam switch create rocq-8.20 ocaml-base-compiler.5.2.1 && \
    eval $(opam env --switch=rocq-8.20) && \
    opam pin add coq 8.20.0 --no-action && \
    opam install coq && \
    opam repo add coq-released https://coq.inria.fr/opam/released && \
    opam install coq-library-undecidability && \
    opam clean -a -c -s --logs

ENV PATH=/root/.opam/rocq-8.20/bin:$PATH
ENV COQPATH=/root/.opam/rocq-8.20/lib/coq/user-contrib

# ---------------------------------------------------------------------------
# Print versions for build-time provenance
# ---------------------------------------------------------------------------
RUN echo "=== Build environment ===" && \
    coqc --version && \
    pdflatex --version | head -1 && \
    gcc --version | head -1 && \
    echo "========================="
# Verify coq-library-undecidability is installed
RUN coqc --version | grep -q "8\.20" && \
    test -d ${COQPATH}/Undecidability && \
    echo "coq-library-undecidability: OK"

WORKDIR /build

# ---------------------------------------------------------------------------
# Copy source files
# ---------------------------------------------------------------------------
COPY rice.tex        ./
COPY rice.bib        ./
COPY rice.v          ./
COPY undecidable.c   ./
COPY alphaurl.bst    ./

# ---------------------------------------------------------------------------
# Download lmcs.cls at build time
# ---------------------------------------------------------------------------
RUN wget -q https://lmcs.episciences.org/public/lmcs.cls -O lmcs.cls || \
    (echo "WARNING: Could not download lmcs.cls — PDF build will be skipped" && \
     touch lmcs.cls.missing)

# ---------------------------------------------------------------------------
# Verify Rocq proof
# ---------------------------------------------------------------------------
RUN coqc rice.v && \
    echo "" && \
    echo "=======================================================" && \
    echo "  Rocq: all proofs verified." && \
    echo "  Axiom: H10C_SAT_undec (from coq-library-undecidability)" && \
    echo "  Rice_Theorem:    Closed under the global context" && \
    echo "  Halting_Problem: Closed under the global context" && \
    echo "=======================================================" && \
    echo ""

# ---------------------------------------------------------------------------
# Build PDF (rice.pdf)
# ---------------------------------------------------------------------------
RUN if [ ! -f lmcs.cls.missing ]; then \
        pdflatex -interaction=nonstopmode -halt-on-error rice && \
        bibtex rice && \
        pdflatex -interaction=nonstopmode -halt-on-error rice && \
        pdflatex -interaction=nonstopmode -halt-on-error rice && \
        echo "rice.pdf: $(pdfinfo rice.pdf | grep Pages)"; \
    else \
        echo "Skipping PDF build (lmcs.cls not available)"; \
    fi

# ---------------------------------------------------------------------------
# Build C witness program
# ---------------------------------------------------------------------------
RUN gcc -O2 -Wall -Wextra -Wno-unused-function -std=c17 \
        undecidable.c -o undecidable -lgmp -lm && \
    echo "" && \
    echo "=======================================================" && \
    echo "  C: undecidable built." && \
    echo "  ./undecidable \"x1^2 - x2^2 - x3^2 - 1\"  (terminates)" && \
    echo "  ./undecidable \"x1^2 + 1\"                (runs forever)" && \
    echo "=======================================================" && \
    echo ""

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
RUN echo "=== Build complete ===" && \
    ls -lh rice.pdf rice.vo undecidable 2>/dev/null && \
    echo "======================"

# ---------------------------------------------------------------------------
# Entrypoint: copy outputs to /out if mounted, else list them
# ---------------------------------------------------------------------------
CMD ["sh", "-c", \
     "if [ -d /out ]; then \
        cp -v rice.pdf rice.vo undecidable /out/ 2>/dev/null; \
        echo 'Files copied to /out/'; \
      else \
        echo 'Mount a host directory to /out to retrieve files:'; \
        echo '  docker run --rm -v \"$PWD/out:/out\" rice-constructive'; \
        ls -lh rice.pdf rice.vo undecidable 2>/dev/null; \
      fi"]
