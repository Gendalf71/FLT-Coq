# FLT-Coq reproducible environment
# Build:   docker build -t flt-coq .
# Run CI:  docker run --rm -v "$PWD":/coq -w /coq flt-coq \
#            bash -lc 'coqc -Q . "" FLT-new.v && coqc -Q . "" FLT-old.v'

FROM coqorg/coq:8.20.1

# Set working directory
WORKDIR /coq

# Copy project files (expecting FLT-new.v, FLT-old.v, Makefile, .coqproject, docs/ etc.)
COPY . /coq

# Default command: print versions then suggest build commands
CMD bash -lc "echo 'Coq version:' && coqc -v && \
  echo && echo 'To build:' && \
  echo '  coqc -Q . \"\" FLT-new.v && coqc -Q . \"\" FLT-old.v' && \
  echo 'or: make'"
