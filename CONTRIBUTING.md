# Contributing to FLT-Coq

Thank you for your interest in improving this repository. The goal is **reproducible formalization** of two conditional routes to FLT in Coq, with clear scope and zero `Admitted`.

## Getting started

- Install Coq ≥ 8.19 (or use Docker).
- Build locally:
  ```bash
  make clean && make
  ```
- Or via Docker without installing Coq:
  ```bash
  docker run --rm -v "$PWD":/coq -w /coq coqorg/coq:8.20.1 \
    bash -lc 'coqc -Q . "" FLT-new.v && coqc -Q . "" FLT-old.v'
  ```

## Code layout

- `FLT-new.v` — **Track B (GN(2))**
- `FLT-old.v` — **Track A (Coverage parameter with maximum coverage)**
- `docs/` — PDFs with background and reconstruction notes
- CI builds on `coqorg/coq:8.19.2` and `8.20.1`

## Style & constraints

- **No `Admitted.`** — CI fails if any are present.
- Prefer small, named lemmas with descriptive identifiers.
- Keep imports minimal; avoid unnecessary axioms beyond standard Coq and the explicit section hypotheses for each track.
- Use comments to mark where each article item corresponds to a lemma/theorem (see README mapping tables).

### Naming conventions (suggested)
- Hypotheses/sections: `GN2`, `maximum_coverage`, `normalization_*`
- Bridges: `*_nat`, `*_R`, `INR_*`
- Growth lemmas: `pow*_gt_linear`, `pow_eq_linear_positive`
- Final theorems: `FLT_from_*`, `fermat_last_theorem_*`

## Pull requests

1. Fork and create a feature branch.
2. Ensure `make` passes locally (or the Docker one‑liner).
3. Ensure CI passes on your branch:
   - both `FLT-new.v` and `FLT-old.v` compile;
   - zero `Admitted.` reported.
4. Update README if you add new lemmas or change the mapping tables.
5. If you add files, update `Makefile` and `.coqproject` accordingly.

## Reporting issues

- Use a clear title and include:
  - Coq version (`coqc -v`);
  - Steps to reproduce (commands, branch/commit);
  - Expected vs actual result;
  - Minimal snippet if possible.

## Releases & citation

- After a tagged release, update `CITATION.cff` with the new version/date and, if applicable, the **Zenodo DOI**. Add/refresh the DOI badge in README.

## License

- By contributing, you agree that your contributions will be licensed under the **BSD-3-Clause** license.
