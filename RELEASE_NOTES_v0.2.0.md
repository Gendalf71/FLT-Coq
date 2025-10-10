# FLT-Coq v0.2.0 — Release Notes (2025-10-10)

**Highlights**
- Two conditional routes to FLT formalized side‑by‑side:
  - **Track A (Coverage parameter)** — `FLT-old.v`
  - **Track B (GN(2))** — `FLT-new.v`
- **Reproducibility**: Makefile, `.coqproject`, Docker one‑liner, and GitHub Actions CI
- **No `Admitted` policy**: CI fails if any `Admitted.` remain
- **Documentation**: README with EN/RU sections, article↔lemma mapping tables, `docs/` PDFs
- **Citable**: `CITATION.cff` prepared for Zenodo DOI
- **License**: BSD‑3‑Clause

---

## What’s new compared to previous state
- Split into two explicit Coq scripts (`FLT-old.v`, `FLT-new.v`) reflecting two strategies
- Added CI workflow (`.github/workflows/coq.yml`) building on `coqorg/coq:8.19.2` and `8.20.1`
- Added `Makefile`, `.coqproject`, `LICENSE`, `CITATION.cff`
- Added Docker-based quick check in README
- Rewrote README with clear **scope disclaimer** and tables mapping paper items to Coq lemmas

---

## How to reproduce locally
```bash
make clean && make        # builds both tracks
# or
coqc -Q . "" FLT-new.v
coqc -Q . "" FLT-old.v
```

## How to reproduce with Docker (no local install)
```bash
docker build -t flt-coq .
docker run --rm -v "$PWD":/coq -w /coq flt-coq   bash -lc 'coqc -Q . "" FLT-new.v && coqc -Q . "" FLT-old.v'
```

*(Alternatively, without building an image:)*
```bash
docker run --rm -v "$PWD":/coq -w /coq coqorg/coq:8.20.1   bash -lc 'coqc -Q . "" FLT-new.v && coqc -Q . "" FLT-old.v'
```

---

## Notes for reviewers
- The repository **assumes** an extra premise in each track (Coverage parameter with maximum coverage, or GN(2)) and **derives FLT** under that assumption. The assumptions themselves are **not** proven here.
- PDF documentation resides in `docs/`.
- CI enforces that no `Admitted.` remain and that both tracks compile deterministically on Coq 8.19/8.20.

---

## Next milestones
- Tag **v0.2.1** after minting Zenodo DOI and updating `CITATION.cff` + README badge
- Add dependency graph (`coqdep`) and optional `Docker Compose` for one‑command builds
- (Optional) Add `CONTRIBUTING.md` guidelines for lemma naming and review process
- (Optional) Add `docs/` HTML site (e.g., GitHub Pages) with excerpted explanations
