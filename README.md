
# FLT-Coq — Two Conditional Routes to FLT in Coq

[![Coq CI](https://github.com/gendalf71/FLT-Coq/actions/workflows/coq.yml/badge.svg)](https://github.com/gendalf71/FLT-Coq/actions/workflows/coq.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.xxxxxxx.svg)](https://doi.org/10.5281/zenodo.xxxxxxx)

> **Scope disclaimer / Дисклеймер:**  
> This repository formalizes **two closely-related conditional strategies** to derive FLT in Coq.  
> **Track A — Coverage parameter (global normalizer $o>1$)** with a *maximum-coverage* principle.  
> **Track B — Explicit-base GN(2)**: for any putative $n>2$ counterexample, postulate $2^n = 2\cdot n$.  
> In both tracks, the extra premise is **assumed (not proven)**; Coq verifies the downstream implication to **FLT**.  
> Репозиторий содержит **две тактики**: A) параметр покрытия $o>1$ с принципом максимального покрытия; B) явная гипотеза **GN(2)**. В обоих случаях допущение **принимается**, а Coq проверяет вывод к **ВТФ**.

---

## Tracks overview

### Track A — Coverage parameter (global normalizer $o>1$)  — **file:** `FLT_old.v`

- Postulates a single real $o>1$ (global normalizer) such that any putative solution with $n>2$ forces a **coverage identity** $o^n = 2\cdot \mathrm{INR}(n)$; with **maximum coverage** the same $o$ covers exactly $n\in\{1,2\}$.  
- Coq proves $o=2$ and that $o^n=2\cdot n$ implies $n\in\{1,2\}$, yielding a contradiction for $n>2$.  
- Rationale & mapping are documented in the *old* PDFs (`*_old_*.pdf`).

**Key Coq ingredients (names may vary slightly):**  
`covers_with`, `normalization_gt1`, `maximum_coverage`, `normalization_equation`,  
`pow2_gt_linear`, `pow3_gt_linear`, `pow_eq_linear_positive`,  
`normalization_parameter_is_two`, `normalization_forces_small_exponent`,  
`covers_two_one`, `covers_two_two`, `covers_two_only_small`,  
`covers_two_nat`, `INR_two_mul_nat`,  
`sum_diff_from_parameters_R`, `sum_diff_from_parameters_Z`, `parity_condition_Z`,  
`fermat_last_theorem_from_global_normalization`, `fermat_last_theorem_via_maximum_coverage`.

---

### Track B — Explicit base **GN(2)**  — **file:** `FLT_new.v`

- **GN(2):** for any putative natural solution with $n>2$, **postulate** $2^n = 2\cdot n$.  
- Coq shows $2^n = 2\cdot n \Rightarrow n\in\{1,2\}$ via elementary growth lemmas; contradiction for $n>2$ ⇒ **FLT**.  
- A real “wrapper” $2^n = 2\cdot\mathrm{INR}(n)$ and bridge lemmas connect $\mathbb{R}$ and $\mathbb{N}$.  
- Rationale & mapping are documented in the *new* PDFs (без `old`).

**Key Coq ingredients:**  
`GN2`, `FLT_from_GN2`, real wrapper `GN2_R`, bridges `covers_two_nat`, `INR_two_mul_nat`, `GN2_R_implies_GN2`, growth lemmas `pow2_gt_linear`, `pow3_gt_linear`, `pow_eq_linear_positive`, and parity lemmas `sum_diff_from_parameters_R`, `sum_diff_from_parameters_Z`, `parity_condition_Z`.  
Also: `fermat_last_theorem_from_GN2_R` (via real wrapper).

> **Motivation vs proof / Мотивация vs доказательство.**  
> Параметризация $z:=m^n+p^n,\ x:=m^n-p^n$ и паритетные факты включены как мотивация/проверки согласованности и **не используются** в финальном шаге обеих дорожек.

---

## Quick start

**A) Docker (no local install, matches CI — Coq $8.18.0$):**
```bash
docker run --rm -v "$PWD":/coq -w /coq coqorg/coq:8.18.0 \
  bash -lc 'coqc -Q . "" FLT_new.v && coqc -Q . "" FLT_old.v'
```

**B) Local (Coq $\ge 8.18$):**
```bash
coqc -Q . "" FLT_new.v
coqc -Q . "" FLT_old.v
```

**C) CI**  
GitHub Actions builds inside Docker on `coqorg/coq:8.18.0`; artifacts (`.vo/.glob`) are written to `/tmp`, so the repository stays clean. The workflow fails if any `Admitted.` remain.

---

## Project structure
```
.
├─ FLT_new.v      # Track B: GN(2)
├─ FLT_old.v      # Track A: Coverage parameter (o>1)
├─ README.md
├─ CITATION.cff
├─ LICENSE
├─ .coqproject / Makefile (optional)
└─ docs/
   ├─ Dedenko_FLT_Description_old_en.pdf
   ├─ FLT_Proof_Reconstruction_old_en.pdf
   ├─ Dedenko_FLT_Coq_README_old.pdf
   ├─ Dedenko_FLT_Description_en.pdf
   ├─ FLT_Proof_Reconstruction_en.pdf
   └─ Dedenko_FLT_Coq_README.pdf
```

---

## Article ↔ Coq mapping (Track B — GN(2))

| Article item (new PDFs) | Coq lemma / theorem |
|---|---|
| Algebraic parametrization over $\mathbb{R}$; integer parity facts over $\mathbb{Z}$ | `sum_diff_from_parameters_R`, `sum_diff_from_parameters_Z`, `parity_condition_Z` |
| GN(2) hypothesis over $\mathbb{N}$ | `GN2` |
| Growth vs. linear; from $2^n = 2\cdot n$ infer $n\in\{1,2\}$ | `pow2_gt_linear`, `pow3_gt_linear`, `pow_eq_linear_positive` |
| Real wrapper and bridge back to $\mathbb{N}$ | `GN2_R`, `covers_two_nat`, `INR_two_mul_nat`, `GN2_R_implies_GN2` |
| FLT from GN(2) (direct) / via real wrapper | `FLT_from_GN2` / `fermat_last_theorem_from_GN2_R` |

---

## Article ↔ Coq mapping (Track A — Coverage parameter)

| Article item (old PDFs) | Coq lemma / theorem |
|---|---|
| Algebraic parametrization over $\mathbb{R}$; integer parity facts over $\mathbb{Z}$ | `sum_diff_from_parameters_R`, `sum_diff_from_parameters_Z`, `parity_condition_Z` |
| Coverage predicate and bridge to naturals | `covers_with`, `covers_two_nat`, `INR_two_mul_nat` |
| Growth vs. linear; from $o^n = 2\cdot n$ infer $n\in\{1,2\}$ | `pow2_gt_linear`, `pow3_gt_linear`, `pow_eq_linear_positive` |
| Global normalization & maximum coverage (hypotheses/section) | `normalization_gt1`, `maximum_coverage`, `normalization_equation` |
| Consequences: $o=2$ and contradiction for $n>2$ | `normalization_parameter_is_two`, `normalization_forces_small_exponent` |
| Explicit realisation with $o=2$; final FLT corollaries | `covers_two_one`, `covers_two_two`, `covers_two_only_small`, `fermat_last_theorem_from_global_normalization`, `fermat_last_theorem_via_maximum_coverage` |

---

## Mathematical notes (brief)

- Core comparisons are elementary growth inequalities showing that an equality of the form “exponential = linear (in $n$)” forces $n\in\{1,2\}$.  
- Track A assumes a **coverage identity** $o^n = 2\cdot \mathrm{INR}(n)$ induced by any counterexample with a *fixed* $o>1$ and imposes **maximum coverage**; Track B assumes **GN(2)** directly.

**Limitations / Ограничения.**  
Ни в одной дорожке допущение не доказывается внутри репозитория; Coq проверяет **следствие** к FLT при указанных предпосылках. Паритет/параметризация — мотивация, не задействованы в финальном шаге.

---

## Cite / Как ссылаться

See `CITATION.cff` (GitHub/Zenodo).

## License

BSD-3-Clause — см. `LICENSE`.
