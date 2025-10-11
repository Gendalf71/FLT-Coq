# FLT-Coq reproducible environment
# Build image:   docker build -t flt-coq .
# Run compile:   docker run --rm -v "$PWD":/coq -w /coq flt-coq \
#                  bash -lc 'coqc -Q . "" FLT_new.v && coqc -Q . "" FLT_old.v'

FROM coqorg/coq:8.18.0

# Set working directory inside the container
WORKDIR /coq

# Copy project files into the image (optional; you can also mount the repo at runtime)
COPY . /coq

# Default command: show Coq version and suggest build commands
CMD bash -lc "echo 'Coq version:' && coqc --version && \
  echo && echo 'To build inside the container run:' && \
  echo '  coqc -Q . \"\" FLT_new.v && coqc -Q . \"\" FLT_old.v' && \
  echo 'or: make'"
