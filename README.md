# FLT‑Coq — Global Normalization (single‑module)

[![Coq CI](https://github.com/gendalf71/FLT-Coq/actions/workflows/coq.yml/badge.svg)](https://github.com/gendalf71/FLT-Coq/actions/workflows/coq.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.17329464.svg)](https://doi.org/10.5281/zenodo.17329464)

> **Scope / Дисклеймер**
>
> This repository contains a **single Coq module** `GlobalNormalization` that formalizes the *coverage‑parameter* route to FLT.  
> The approach **assumes** that any putative counterexample with $n>2$ induces a *coverage identity* for a fixed real $o>1$:
> $$o^n \;=\; 2\cdot \mathrm{INR}(n).$$
> Under the **maximum‑coverage** principle this forces $o=2$ and further implies $n\in\{1,2\}$, contradicting $n>2$ and hence yielding **FLT**.  
> В репозитории представлена **одна** дорожка с параметром покрытия $o>1$; допущение принимается как гипотеза, а Coq проверяет вывод к **ВТФ**.

---

## File

- **`GlobalNormalization.v`** — all definitions, auxiliary lemmas (marked `#[local]`), main “bridge”, maximum‑coverage theorem, FLT corollaries, and end‑of‑file sanity goals.

If you only want the public interface, the module ends with:
```coq
Export GlobalNormalization.v.
```
so you can simply `Require Import GlobalNormalization.` and use the exported names.

---

## How to build

**A) Docker (matches CI, Coq 8.18.0)**
```bash
docker run --rm -v "$PWD":/coq -w /coq coqorg/coq:8.18.0 \
  bash -lc 'coqc -Q . "" GlobalNormalization.v'
```

**B) Local (Coq ≥ 8.18)**
```bash
coqc -Q . "" GlobalNormalization.v
```

---

## What the module proves (informally)

- **Coverage predicate.** `covers_with o n : Prop` is the equality
  $$o^n \;=\; 2\cdot \mathrm{INR}(n).$$

- **Bridge from two normalizations to a natural power identity.**  
  `two_real_normalizations_imply_nat_power_eq` shows that $o^n=2\cdot\mathrm{INR}(n)$ and $o^m=2\cdot\mathrm{INR}(m)$ imply
  $$(2n)^m = (2m)^n \quad\text{over } \mathbb{N}.$$

- **Maximum coverage forces small exponents and $o=2$.**  
  `maximum_coverage_as_theorem` yields $o=2$ and `covers_with 2 n → n∈{1,2}`.

- **FLT corollaries (conditional).**  
  From the hypothesis that any putative $(x,y,z,n)$ with $n>2$ satisfies `covers_with o n`, Coq derives a contradiction for $n>2$ via
  `normalization_parameter_is_two`, `normalization_forces_small_exponent` and the corollaries
  `fermat_last_theorem_from_global_normalization` and
  `fermat_last_theorem_via_maximum_coverage` (real wrapper $2^n=2\cdot\mathrm{INR}(n)$).

**Auxiliaries used internally (marked `#[local]`).**  
Arithmetic over $\mathbb{Z}$: binomial divisibility and parity for $z:=m^n+p^n$, $x:=m^n-p^n$.  
Arithmetic over $\mathbb{N}$ and $\mathbb{R}$: elementary growth lemmas showing that an identity of the form “exponential $=$ linear” forces $n\in\{1,2\}$.

---

## Key definitions and lemmas (selection)

- `covers_with (o: R) (n: nat) : Prop` — $o^n=2\cdot\mathrm{INR}(n)$.
- **Public results:**  
  `covers_with_one_forces_two`, `two_real_normalizations_imply_nat_power_eq`,  
  `covers_with_two_characterisation`, `maximum_coverage_as_theorem`,  
  `normalization_parameter_is_two`, `normalization_forces_small_exponent`,  
  `fermat_last_theorem_from_global_normalization`, `fermat_last_theorem_via_maximum_coverage`.
- **Internals (`#[local]`):** parity/divisibility over $\mathbb{Z}$, growth lemmas (`pow2_gt_linear`, `pow_eq_linear_positive`), real–nat bridges (`covers_two_nat`, `INR_two_mul_nat`, etc.).

---

## Using the module

```coq
From Coq Require Import Reals Arith.
Require Import GlobalNormalization.

(* Example: you can refer to the public lemmas directly *)
Check covers_with_one_forces_two.
Check maximum_coverage_as_theorem.
```

The end of `GlobalNormalization.v` contains **sanity goals** (quick regression checks) like:
$$\texttt{covers\_with\ 2\ 3 -> False} \quad\text{and}\quad\forall n>2,\ \texttt{covers\_with\ 2\ n -> False}.$$

---

## Limitations / Ограничения

This is a **conditional** development: the coverage identity is **assumed**, not proven. The module shows that this assumption is sufficient to derive FLT. Паритетные и параметрические леммы служат проверками согласованности и не задействованы в финальном шаге.

---

## License / Citation

- License: **BSD‑3‑Clause** (`LICENSE`).
- Cite via `CITATION.cff` / Zenodo badge above.
