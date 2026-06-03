# FLT‑Coq — Logarithmic Zero‑Gap Obstruction, Version 16.4

[![Coq CI](https://github.com/gendalf71/FLT-Coq/actions/workflows/coq.yml/badge.svg)](https://github.com/gendalf71/FLT-Coq/actions/workflows/coq.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.17329464.svg)](https://doi.org/10.5281/zenodo.17329464)

> **Scope / Disclaimer / Дисклеймер**
>
> This repository contains a single Coq file, `GlobalNormalization.v`. The filename is kept for
> backward compatibility with earlier repository references. In Version 16.4, its mathematical
> content is the conditional **logarithmic zero‑gap obstruction** / **logarithmic
> coefficient‑symmetry compatibility** development.
>
> The development is conditional. Coq does **not** prove Fermat's Last Theorem without additional
> assumptions. It verifies the formal consequences of explicitly stated real factorizations of one
> odd binomial core, positivity of residual factors, and the zero‑logarithmic‑gap condition.
>
> В репозитории сохранено имя файла `GlobalNormalization.v` для совместимости с прежними
> ссылками. В версии 16.4 математическое содержание файла соответствует логарифмическому
> препятствию совместимости с нулевым зазором. Coq не доказывает ВТФ без дополнительных
> предпосылок, а проверяет условную формальную цепочку.

---

## File

- **`GlobalNormalization.v`** — a single Coq file containing:
  - real‑parameter identities;
  - integer‑parameter specialization and parity checks;
  - the modular caveat;
  - the two real factorizations of the odd binomial core;
  - the algebraic comparison of residual factors;
  - the logarithmic gap $\Delta_n=\ln(l/q)$;
  - the zero‑logarithmic‑gap condition;
  - the bridge between residual‑scale equality and zero logarithmic gap;
  - the equivalence with coefficient‑mass equality;
  - the final elementary growth obstruction.

The filename `GlobalNormalization.v` is retained for compatibility with older references to this
repository. The current mathematical reading is Version 16.4: logarithmic zero‑gap obstruction.

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

## What the module proves informally

### 1. Real, integer, modular, and logarithmic levels

The file separates several levels of reasoning:

- real‑parameter identities for expressions of the form $z=m^n+p^n$ and $x=m^n-p^n$;
- integer specialization and parity conditions;
- modular congruence caveats;
- the logarithmic zero‑gap layer.

Relevant Coq names include:

```coq
sum_diff_from_parameters_R
sum_diff_from_parameters_Z
parity_condition_Z
no_parameters_if_parity_violation
no_parameters_if_odd
no_parameters_for_example
ModularRemark
modular_congruence_not_integer_equality
```

### 2. Two real factorizations of the same core

Version 16.4 uses two real representations of one odd binomial core:

$$
\mathrm{core}=n\,l^n,
\qquad
\mathrm{core}=2^{n-1}q^n.
$$

Relevant Coq definitions:

```coq
real_core_factorization
coefficient_mass_factorization
```

### 3. Algebraic compatibility relation

From the two factorizations of the same core, Coq proves the exact relation

$$
l^n=q^n\frac{2^{n-1}}{n}.
$$

Relevant Coq lemma:

```coq
two_scale_factorizations_relation
```

### 4. Logarithmic gap

For positive residual factors $l>0$ and $q>0$, Version 16.4 introduces the logarithmic gap

$$
\Delta_n := \ln(l/q).
$$

The exact algebraic relation can then be written as

$$
\Delta_n
=
\frac{1}{n}\ln\frac{2^{n-1}}{n}.
$$

Relevant Coq definitions:

```coq
logarithmic_gap
zero_logarithmic_gap
coefficient_logarithmic_gap
```

The entropy‑type language, if used, is heuristic only. In Coq and in the strict mathematical content,
this is just a real logarithmic comparison of positive quantities.

### 5. Zero‑gap equivalence

Coq formalizes the bridge

$$
l^n=q^n
\quad\Longleftrightarrow\quad
\Delta_n=0.
$$

Relevant Coq lemmas:

```coq
residual_scale_equality_implies_zero_logarithmic_gap
zero_logarithmic_gap_implies_residual_scale_equality
residual_scale_equality_iff_zero_logarithmic_gap
```

### 6. Version 16.4 central chain

Coq defines:

```coq
residual_scale_equality
coefficient_mass_equality
```

with the meanings

$$
l^n=q^n
$$

and

$$
n=2^{n-1}.
$$

The central Version 16.4 chain is

$$
l^n=q^n
\quad\Longleftrightarrow\quad
\Delta_n=0
\quad\Longleftrightarrow\quad
n=2^{n-1}.
$$

Relevant Coq theorems:

```coq
coefficient_symmetry_compatibility_iff
logarithmic_coefficient_symmetry_compatibility_iff
logarithmic_zero_gap_chain
```

The earlier algebraic core is retained, but Version 16.4 adds the logarithmic zero‑gap layer on top
of it.

### 7. Final obstruction

Coq verifies the elementary exponential‑linear obstruction:

```coq
binary_scaling_roots_only_one_two
```

which proves informally:

$$
n=2^{n-1}
\quad\Longrightarrow\quad
n\in\{1,2\}.
$$

The final conditional high‑exponent exclusions are represented by:

```coq
logarithmic_data_forces_shift
logarithmic_data_forces_small_exponent
logarithmic_data_excludes_high_exponent
logarithmic_zero_gap_excludes_high_exponent
```

Thus, under the two real factorizations, positivity of $l,q$, and the zero‑logarithmic‑gap condition
$\Delta_n=0$, the case $n>2$ is impossible.

---

## Key definitions and lemmas (selection)

- `real_core_factorization` — real factorization of the core as $\mathrm{core}=n\,l^n$.
- `coefficient_mass_factorization` — real factorization of the core as $\mathrm{core}=2^{n-1}q^n$.
- `two_scale_factorizations_relation` — comparison of the two factorizations.
- `residual_scale_equality` — the equality $l^n=q^n$.
- `coefficient_mass_equality` — the equality $n=2^{n-1}$.
- `coefficient_symmetry_compatibility_iff` — the algebraic compatibility equivalence retained in
  Version 16.4.
- `CoefficientSymmetryData` — record packaging the exponent, core, residual scales, positivity,
  the two factorizations, and residual‑scale equality.
- `binary_scaling_roots_only_one_two` — final elementary growth obstruction.
- `ModularRemark` and `modular_congruence_not_integer_equality` — modular caveat.
- `logarithmic_gap` — real logarithmic gap $\ln(l/q)$.
- `zero_logarithmic_gap` — the condition $\ln(l/q)=0$.
- `coefficient_logarithmic_gap` — the coefficient‑side expression
  $\frac{1}{n}\ln\frac{2^{n-1}}{n}$.
- `residual_scale_equality_implies_zero_logarithmic_gap` — from residual‑scale equality to zero gap.
- `zero_logarithmic_gap_implies_residual_scale_equality` — from zero gap to residual‑scale equality.
- `residual_scale_equality_iff_zero_logarithmic_gap` — equivalence between the two conditions.
- `logarithmic_coefficient_symmetry_compatibility_iff` — equivalence between zero gap and
  coefficient‑mass equality under the two factorizations.
- `logarithmic_zero_gap_chain` — the Version 16.4 chain
  $l^n=q^n \Longleftrightarrow \Delta_n=0 \Longleftrightarrow n=2^{n-1}$.
- `LogarithmicCoefficientSymmetryData` — record packaging the exponent, core, residual factors,
  positivity, the two factorizations, and the zero‑logarithmic‑gap condition.
- `logarithmic_data_forces_shift` — derives $n=2^{n-1}$ from packaged logarithmic data.
- `logarithmic_data_forces_small_exponent` — derives $n\in\{1,2\}$.
- `logarithmic_data_excludes_high_exponent` — excludes $n>2$ from packaged logarithmic
  compatibility data.
- `logarithmic_zero_gap_excludes_high_exponent` — final conditional high‑exponent exclusion.

---

## Using the module

```coq
From Coq Require Import Reals Arith.
Require Import GlobalNormalization.

Check real_core_factorization.
Check coefficient_mass_factorization.
Check two_scale_factorizations_relation.
Check residual_scale_equality.
Check coefficient_mass_equality.
Check logarithmic_gap.
Check zero_logarithmic_gap.
Check coefficient_logarithmic_gap.
Check residual_scale_equality_iff_zero_logarithmic_gap.
Check logarithmic_coefficient_symmetry_compatibility_iff.
Check logarithmic_zero_gap_chain.
Check LogarithmicCoefficientSymmetryData.
Check logarithmic_zero_gap_excludes_high_exponent.
Check binary_scaling_roots_only_one_two.
```

If your local version wraps these names inside an explicit Coq module namespace, qualify the names
accordingly.

---

## Sanity checks

The end of `GlobalNormalization.v` may contain quick regression checks around the current public
interface, for example checks involving:

```coq
residual_scale_equality_iff_zero_logarithmic_gap
logarithmic_coefficient_symmetry_compatibility_iff
logarithmic_zero_gap_chain
binary_scaling_roots_only_one_two
logarithmic_zero_gap_excludes_high_exponent
```

The intended informal summary is:

$$
\mathrm{core}=n\,l^n,
\qquad
\mathrm{core}=2^{n-1}q^n
$$

imply

$$
l^n=q^n\frac{2^{n-1}}{n}.
$$

For $l>0$ and $q>0$, define

$$
\Delta_n:=\ln(l/q).
$$

Then the Version 16.4 central chain is:

$$
l^n=q^n
\quad\Longleftrightarrow\quad
\Delta_n=0
\quad\Longleftrightarrow\quad
n=2^{n-1}.
$$

And since

$$
n=2^{n-1}
\quad\Longrightarrow\quad
n\in\{1,2\},
$$

the zero‑logarithmic‑gap condition is compatible only with the linear and quadratic cases and is
incompatible with every exponent higher than the square.

---

## What Coq does not prove

Coq does not prove Fermat's Last Theorem without additional assumptions.

Coq also does not prove that every hypothetical positive integer solution must force the zero‑gap
condition

$$
\Delta_n=0.
$$

What Coq verifies is the formal conditional chain: if the following premises are explicitly given,

- two real factorizations of the same odd binomial core;
- positivity of $l$ and $q$;
- zero‑logarithmic‑gap condition $\Delta_n=0$;

then one obtains

$$
n=2^{n-1},
$$

and therefore

$$
n\in\{1,2\}.
$$

The decisive mathematical question remains outside the purely formal final chain: must the internal
two‑power symmetry of a hypothetical positive integer solution force the zero‑logarithmic‑gap
condition $\Delta_n=0$? The Coq development makes this boundary explicit.

---

## Limitations / Ограничения

This is a **conditional** development. The two real factorizations, positivity of the residual factors,
and the zero‑logarithmic‑gap condition are explicit premises of the compatibility framework. Coq
verifies the consequences of these premises, including the bridge between residual‑scale equality and
zero logarithmic gap, the equivalence with coefficient‑mass equality, and the final exclusion of
exponents greater than two. It does not prove the zero‑gap condition from an arbitrary hypothetical
integer solution of Fermat's equation.

Это **условная** разработка. Две вещественные факторизации, положительность остаточных
множителей и условие нулевого логарифмического зазора являются явными предпосылками схемы
совместимости. Coq проверяет следствия этих предпосылок, включая переход между равенством
остаточных масштабов и нулевым логарифмическим зазором, эквивалентность с равенством
коэффициентных масс и финальное исключение показателей больше двух. Coq не доказывает
условие нулевого логарифмического зазора из произвольного гипотетического целочисленного
решения уравнения Ферма.

---

## License / Citation

- License: **BSD‑3‑Clause** (`LICENSE`).
- Cite via `CITATION.cff` / Zenodo badge above.
