# FLT-Coq v0.2.0 — Release Notes (2025-10-10)

**Highlights**
- Two conditional routes to FLT formalized side‑by‑side:
  - **Track A (Coverage parameter)** — `FLT_old.v`
  - **Track B (GN(2))** — `FLT_new.v`
- **Reproducibility**: Makefile, `.coqproject`, Docker one‑liner, and GitHub Actions CI
- **No `Admitted` policy**: CI fails if any `Admitted.` remain
- **Documentation**: README with overview + article↔lemma mapping tables; PDFs in `new/` and `old/`
- **Citable**: `CITATION.cff` prepared for Zenodo DOI
- **License**: BSD‑3‑Clause

---

## What’s new compared to previous state
- Split into two explicit Coq scripts (`FLT_old.v`, `FLT_new.v`) reflecting two strategies
- Added CI workflow (`.github/workflows/coq.yml`) using Docker on `coqorg/coq:8.18.0`
- Added `Makefile`, `.coqproject`, `LICENSE`, `CITATION.cff`
- Added Docker-based quick check in README
- Rewrote README with clear **scope disclaimer** and tables mapping paper items to Coq lemmas

---

## How to reproduce locally
```bash
make clean && make        # builds both tracks
# or
coqc -Q . "" FLT_new.v
coqc -Q . "" FLT_old.v
```

## How to reproduce with Docker (no local install)
```bash
docker run --rm -v "$PWD":/coq -w /coq coqorg/coq:8.18.0   bash -lc 'coqc -Q . "" FLT_new.v && coqc -Q . "" FLT_old.v'
```

---

## Notes for reviewers
- The repository **assumes** an extra premise in each track (Coverage parameter with maximum coverage, or GN(2)) and **derives FLT** under that assumption. The assumptions themselves are **not** proven here.
- PDF documentation resides in `new/` and `old/` (historical notes also under `add-once/`).
- CI compiles on Coq **8.18.0** inside Docker, writes artifacts to `/tmp`, and enforces that no `Admitted.` remain.

---

## Next milestones
- Tag **v0.2.1** after minting Zenodo DOI and updating `CITATION.cff` + README badge
- Prepare compatibility patch for Coq 8.19+/8.20+ (explicit scopes `%Z/%nat`, `Z.of_nat`, imports)
- Add dependency graph (`coqdep`) and optional `Docker Compose` for one‑command builds
- (Optional) Add `docs/` HTML (GitHub Pages) with excerpted explanations
