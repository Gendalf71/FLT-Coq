# Pull Request

## Summary
Short description of the change.

## What changed
- [ ] Track A (Coverage) — `FLT-old.v`
- [ ] Track B (GN(2)) — `FLT-new.v`
- [ ] Docs (`docs/`)
- [ ] Build/CI (`Makefile`, `.coqproject`, `.github/workflows`)
- [ ] Repo metadata (`CITATION.cff`, `LICENSE`, README)

## Reproducibility
- [ ] `make clean && make` passes locally
- [ ] Docker one-liner passes:
  ```bash
  docker run --rm -v "$PWD":/coq -w /coq coqorg/coq:8.20.1     bash -lc 'coqc -Q . "" FLT-new.v && coqc -Q . "" FLT-old.v'
  ```
- [ ] CI is green

## No-Admitted check
- [ ] `tools/check-admitted.sh` returns **OK** (no `Admitted.`)

## Mapping tables / README
- [ ] Updated tables mapping article items ↔ Coq lemmas if names changed
- [ ] README quick-start remains accurate

## Notes for reviewers
Anything you want the reviewers to focus on.
