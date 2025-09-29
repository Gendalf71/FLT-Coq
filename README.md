# FLT-Coq — Conditional FLT via GN(2): $2^n = 2\cdot n$

> Coq formalization of a **conditional** route to Fermat’s Last Theorem (FLT) based on an explicit-base hypothesis GN(2). The single assumption is:
>
> **GN(2).** For any $n>2$ and any $x,y,z \in \mathbb{N}$,
>
> $$x^n + y^n = z^n \ \Rightarrow\ 2^n = 2\cdot n.$$
>
> Together with the elementary fact that $2^n > 2\cdot n$ for all $n \ge 3$, this yields an immediate contradiction; hence no natural solutions exist for $n>2$ (FLT).
>
> The assumption GN(2) is not proven here; it is isolated as a single hypothesis under which a short, elementary contradiction follows.

---

## What is formalized (Coq)

- **Motivation (algebra over $\mathbb{R}$ / parity over $\mathbb{Z}$)** — not used in the final step
  - `sum_diff_from_parameters_R` (over reals): from $z := m^n + p^n$, $x := m^n - p^n$ derive $z+x = 2\cdot m^n$, $z-x = 2\cdot p^n$.
  - `sum_diff_from_parameters_Z`, `parity_condition_Z`: specialization to integers; in particular $z \pm x$ are even.
  - `no_parameters_if_parity_violation`, `no_parameters_if_odd`, `no_parameters_for_example`: rule out integer parameters when parity contradicts the required evenness.
- **Elementary growth lemmas (used in the core)**
  - `pow2_gt_linear`, `pow3_gt_linear`: exponential vs. linear growth.
  - `pow_eq_linear_positive`: from $2^n = 2\cdot n$ infer $n \in \{1,2\}$.
- **GN(2) core over naturals**
  - `Definition GN2 : Prop` encodes the hypothesis
    ```coq
    forall (n x y z : nat),
      2 < n ->
      Nat.pow x n + Nat.pow y n = Nat.pow z n ->
      2 ^ n = 2 * n.
    ```
  - `FLT_from_GN2`: from `GN2` derive a contradiction for any putative counterexample with `n > 2`.
- **Real “wrapper” and bridge back to $\mathbb{N}$ (optional)**
  - `covers_two_nat`, `INR_two_mul_nat`: identities linking reals and naturals.
  - `GN2_R`: real coverage predicate $ \mathrm{pow}\,2\,n = 2\cdot \mathrm{INR}\,n $ for any putative counterexample.
  - `GN2_R_implies_GN2`: bridge from the real predicate to the natural equality.
  - `fermat_last_theorem_from_GN2_R`: FLT from the real wrapper via the bridge.

**Scope note.** The $\mathbb{R}/\mathbb{Z}$ parametrization and parity lemmas document consistency checks and motivation; they are not needed in the final GN(2) $\Rightarrow$ FLT step.

---

## Build & check

```bash
coqc FLT.v
```
- Compiles with no `Admitted`.
- Uses standard Coq libraries (`Arith`, `Lia`, `Reals`, `ZArith`, `Ring`).

---

## Text ↔ Coq map

- Real parametrization: `sum_diff_from_parameters_R`
- Integer parametrization & parity: `sum_diff_from_parameters_Z`, `parity_condition_Z`
- Parity obstruction example: `no_parameters_for_example`
- Growth lemmas: `pow2_gt_linear`, `pow3_gt_linear`
- Linear = exponential only for $n=1,2$: `pow_eq_linear_positive`
- GN(2) hypothesis over $\mathbb{N}$: `GN2`
- FLT from GN(2): `FLT_from_GN2`
- Real wrapper and bridge: `covers_two_nat`, `INR_two_mul_nat`, `GN2_R`, `GN2_R_implies_GN2`, `fermat_last_theorem_from_GN2_R`

---

## PDFs

- Russian (latest): see repository PDFs and: <https://www.researchgate.net/publication/381293382_OSTRYE_UGLY_V_RASSUZDENII_PERA_FERMA_O_NERAZLOZIMOSTI_STEPENI_VYSE_KVADRATA_OBZOR>
- English (latest): see repository PDFs and: <https://doi.org/10.13140/RG.2.2.24342.32321>

---

# FLT-Coq (Русский)

## Главная (условная) формулировка

**ГН(2).** Для любого $n>2$ и любых $x,y,z \in \mathbb{N}$

$ x^n + y^n = z^n \ \Rightarrow\ 2^n = 2\cdot n. $


Вместе с элементарным фактом $2^n > 2\cdot n$ для всех $n \ge 3$ это даёт немедленное противоречие; следовательно, решений в натуральных числах при $n>2$ не существует (ВТФ).

Гипотеза ГН(2) здесь не доказывается; это единственное допущение, из которого коротко получается противоречие.

---

## Что формализовано (Coq)

- **Мотивация (алгебра над $\mathbb{R}$ / чётность над $\mathbb{Z}$)** — в финальном шаге не используется
  - `sum_diff_from_parameters_R`: из $z := m^n + p^n$, $x := m^n - p^n$ получаем $z+x = 2\cdot m^n$, $z-x = 2\cdot p^n$.
  - `sum_diff_from_parameters_Z`, `parity_condition_Z`: специализация на целые; в частности $z \pm x$ чётны.
  - `no_parameters_if_parity_violation`, `no_parameters_if_odd`, `no_parameters_for_example`: исключают параметры при несогласованной чётности.
- **Элементарные леммы роста (используются в ядре)**
  - `pow2_gt_linear`, `pow3_gt_linear`: экспонента против линейной.
  - `pow_eq_linear_positive`: из $2^n = 2\cdot n$ следует $n \in \{1,2\}$.
- **Ядро ГН(2) над натуральными**
  - `GN2` — гипотеза в терминах $\mathbb{N}$ (см. код выше).
  - `FLT_from_GN2` — из `GN2` получаем противоречие при любом $n>2$.
- **Вещественная “оболочка” и мост обратно в $\mathbb{N}$ (опционально)**
  - `covers_two_nat`, `INR_two_mul_nat`: связи $\mathbb{R} \leftrightarrow \mathbb{N}$.
  - `GN2_R`: предикат покрытия $ \mathrm{pow}\,2\,n = 2\cdot \mathrm{INR}\,n $ для любого гипотетического контрпримера.
  - `GN2_R_implies_GN2`: мост к равенству в $\mathbb{N}$.
  - `fermat_last_theorem_from_GN2_R`: ВТФ из вещественной оболочки через мост.

---

## Сборка и проверка

```bash
coqc FLT.v
```
- Компилируется без `Admitted`.
- Используются стандартные библиотеки Coq (`Arith`, `Lia`, `Reals`, `ZArith`, `Ring`).

---

## Соответствие текст ↔ Coq

- Параметризация над $\mathbb{R}$: `sum_diff_from_parameters_R`
- Параметризация и чётность над $\mathbb{Z}$: `sum_diff_from_parameters_Z`, `parity_condition_Z`
- Пример препятствия по чётности: `no_parameters_for_example`
- Леммы роста: `pow2_gt_linear`, `pow3_gt_linear`
- Равенство $2^n = 2\cdot n$ только при $n=1,2$: `pow_eq_linear_positive`
- Гипотеза ГН(2) над $\mathbb{N}$: `GN2`
- ВТФ из ГН(2): `FLT_from_GN2`
- Вещественная оболочка и мост: `covers_two_nat`, `INR_two_mul_nat`, `GN2_R`, `GN2_R_implies_GN2`, `fermat_last_theorem_from_GN2_R`

---

© 2025. Conditional formalization “GN(2) $\Rightarrow$ FLT”.
