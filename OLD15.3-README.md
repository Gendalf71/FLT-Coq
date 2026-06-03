# FLT‑Coq — Coefficient‑Symmetry Compatibility, Version 15.3

[![Coq CI](https://github.com/gendalf71/FLT-Coq/actions/workflows/coq.yml/badge.svg)](https://github.com/gendalf71/FLT-Coq/actions/workflows/coq.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.17329464.svg)](https://doi.org/10.5281/zenodo.17329464)

> **Scope / Disclaimer / Дисклеймер**
>
> This repository contains a single Coq file, `GlobalNormalization.v`. The filename is kept for
> backward compatibility with earlier repository references, but the current Version 15.3 is formulated
> as a conditional **coefficient‑symmetry compatibility** / **residual‑scale compatibility** development.
>
> The development is conditional. Coq does **not** prove Fermat's Last Theorem unconditionally. It
> verifies the formal consequences of explicitly stated real factorizations of one odd binomial core
> and of a residual‑scale compatibility requirement.
>
> В репозитории сохранено имя файла `GlobalNormalization.v` для совместимости с прежними
> ссылками. Текущая логика версии 15.3 формулируется через сравнение двух естественных
> вещественных нормировок одного и того же нечётного биномиального ядра и через препятствие
> совместимости остаточных масштабов.

---

## File

- **`GlobalNormalization.v`** — a single Coq file containing:
  - real‑parameter identities;
  - integer‑parameter specialization and parity checks;
  - the modular caveat;
  - the two real factorizations of the odd binomial core;
  - the residual‑scale compatibility relation;
  - the equivalence between residual‑scale equality and coefficient‑mass equality;
  - the final elementary growth obstruction.

The filename `GlobalNormalization.v` is retained for compatibility with older references to this
repository. The current mathematical reading is the Version 15.3 coefficient‑symmetry compatibility
framework.

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

### 1. Real and integer parameter levels

The file separates several levels of reasoning:

- real‑parameter identities for expressions of the form $z=m^n+p^n$ and $x=m^n-p^n$;
- integer specialization and parity conditions;
- modular congruence caveats.

Relevant Coq names include:

```coq
sum_diff_from_parameters_R
sum_diff_from_parameters_Z
parity_condition_Z
no_parameters_if_parity_violation
no_parameters_if_odd
no_parameters_for_example
```

### 2. Two real factorizations of the same core

Version 15.3 uses two real representations of one odd binomial core:

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

### 3. Compatibility relation

From the two factorizations of the same core, Coq proves the exact relation

$$
l^n=q^n\frac{2^{n-1}}{n}.
$$

Relevant Coq lemma:

```coq
two_scale_factorizations_relation
```

### 4. Version 15.3 equivalence

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

The central theorem is:

```coq
coefficient_symmetry_compatibility_iff
```

It formalizes the Version 15.3 equivalence:

$$
l^n=q^n
\quad\Longleftrightarrow\quad
n=2^{n-1}.
$$

### 5. Final obstruction

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

Finally, the conditional high‑exponent exclusions are represented by:

```coq
coefficient_symmetry_data_excludes_high_exponent
coefficient_symmetry_compatibility_excludes_high_exponent
```

Thus, under the two factorizations and the residual‑scale equality, the case $n>2$ is impossible.

---

## Key definitions and lemmas (selection)

- `real_core_factorization` — real factorization of the core as $\mathrm{core}=n\,l^n$.
- `coefficient_mass_factorization` — real factorization of the core as $\mathrm{core}=2^{n-1}q^n$.
- `two_scale_factorizations_relation` — comparison of the two factorizations.
- `residual_scale_equality` — the equality $l^n=q^n$.
- `coefficient_mass_equality` — the equality $n=2^{n-1}$.
- `residual_scale_equality_forces_coefficient_mass_equality` — the forward direction.
- `coefficient_mass_equality_forces_residual_scale_equality` — the reverse direction.
- `coefficient_symmetry_compatibility_iff` — the central Version 15.3 equivalence.
- `CoefficientSymmetryData` — record packaging the exponent, core, residual scales, positivity,
  the two factorizations, and residual‑scale equality.
- `coefficient_symmetry_data_forces_shift` — derives $n=2^{n-1}$ from packaged data.
- `coefficient_symmetry_data_forces_small_exponent` — derives $n\in\{1,2\}$.
- `coefficient_symmetry_data_excludes_high_exponent` — excludes $n>2$ from the packaged
  compatibility data.
- `coefficient_symmetry_compatibility_excludes_high_exponent` — final conditional high‑exponent
  exclusion.
- `ModularRemark` and `modular_congruence_not_integer_equality` — modular caveat.

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
Check coefficient_symmetry_compatibility_iff.
Check coefficient_symmetry_compatibility_excludes_high_exponent.
```

If your local version wraps these names inside an explicit Coq module namespace, qualify the names
accordingly.

---

## Sanity checks

The end of `GlobalNormalization.v` may contain quick regression checks around the current public
interface, for example checks involving:

```coq
coefficient_symmetry_compatibility_iff
binary_scaling_roots_only_one_two
coefficient_symmetry_compatibility_excludes_high_exponent
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

Therefore,

$$
l^n=q^n
\quad\Longleftrightarrow\quad
n=2^{n-1}.
$$

And since

$$
n=2^{n-1}
\quad\Longrightarrow\quad
n\in\{1,2\},
$$

the residual‑scale equality is compatible only with the linear and quadratic cases and is
incompatible with every exponent higher than the square.

---

## What Coq does not prove

Coq does not prove Fermat's Last Theorem unconditionally.

Coq also does not prove that every hypothetical positive integer solution must preserve the
residual‑scale equality

$$
l^n=q^n.
$$

What Coq verifies is the formal conditional chain: if the two real factorizations and the
residual‑scale equality are given as premises, then the exponent is forced into the set
$\{1,2\}$, and therefore the case $n>2$ is excluded.

The decisive mathematical question remains outside the purely formal final chain: must the internal
two‑power symmetry of a hypothetical positive integer solution preserve the equality of residual
scales between the two natural real normalizations of the same odd binomial core? The Coq development
makes this boundary explicit.

---

## Limitations / Ограничения

This is a **conditional** development. The two real factorizations and the residual‑scale equality
are explicit premises of the compatibility framework. Coq verifies the consequences of these
premises, including the equivalence between residual‑scale equality and coefficient‑mass equality,
and the final exclusion of exponents greater than two. It does not prove the residual‑scale equality
from an arbitrary hypothetical integer solution of Fermat's equation.

Это **условная** разработка. Две вещественные факторизации и равенство остаточных масштабов
являются явными предпосылками схемы совместимости. Coq проверяет следствия этих предпосылок,
включая эквивалентность между равенством остаточных масштабов и равенством коэффициентных
масс, а также финальное исключение показателей больше двух. Coq не доказывает само равенство
остаточных масштабов из произвольного гипотетического целочисленного решения уравнения Ферма.

---

## License / Citation

- License: **BSD‑3‑Clause** (`LICENSE`).
- Cite via `CITATION.cff` / Zenodo badge above.
