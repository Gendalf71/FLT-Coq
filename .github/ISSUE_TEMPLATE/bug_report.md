---
name: Bug report
about: Report a problem building or verifying the Coq scripts
title: "[BUG] Short description"
labels: bug
assignees: ''
---

## Summary
A clear and concise description of the issue.

## Environment
- OS: [e.g. Ubuntu 22.04]
- Coq: output of `coqc -v`
- Docker image (if used): e.g. `coqorg/coq:8.20.1`
- Commit/tag: [e.g. v0.2.0 / abcdef1]

## Steps to Reproduce
1. Commands you ran (prefer exact copy):
   ```bash
   make clean && make
   # or
   docker run --rm -v "$PWD":/coq -w /coq coqorg/coq:8.20.1      bash -lc 'coqc -Q . "" FLT-new.v && coqc -Q . "" FLT-old.v'
   ```
2. ...

## Expected behavior
What you expected to happen.

## Actual behavior
What actually happened (full error log if possible).

## Artifacts
- Logs (attach or paste)
- Screenshots (optional)
- Minimal code snippet (if not reproducible with repository HEAD)

## Checklist
- [ ] I searched existing issues
- [ ] I can reproduce on both local build and Docker (if possible)
- [ ] I included `coqc -v` output
