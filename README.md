# FLT-Coq — Conditional FLT via “global normalization” \(o^n=2\cdot n\) (Dedenko reading)

> This repository contains a Coq formalization of a *conditional* implication extracted from a reading of G. L. Dedenko’s manuscript: **if one assumes a single “global” normalizing factor \(o>1\) such that for every putative natural counterexample \(x^n+y^n=z^n\) with \(n>2\) one has \(o^n = 2\cdot n\), then Fermat’s Last Theorem holds for all \(n>2\).**

---

## Main (conditional) statement

**Normalization equation (axiom/assumption).**  
There exists a fixed \(o\in\mathbb{N}\) with \(o>1\) such that for every \(n>2\) and every putative solution in naturals,
\[
x^n+y^n=z^n \quad\Longrightarrow\quad o^n = 2\cdot n.
\]

**Consequence.**  
From \(o^n=2\cdot n\) alone, elementary growth lemmas yield only the cases \((o,n)=(2,1)\) and \((2,2)\). Therefore no natural solutions to \(x^n+y^n=z^n\) can exist for any \(n>2\).

This is formalized in Coq as a conditional theorem. The assumption is *not* proved in this project; it is isolated as a single hypothesis under which a short, elementary, “Fermat-style” contradiction follows.

---

## What is formalized (Coq)

- **Real vs integer parametrizations**
  - `sum_diff_from_parameters_R` (over reals): from \(z:=m^n+p^n\), \(x:=m^n-p^n\) we get \(z+x=2\,m^n\) and \(z-x=2\,p^n\).
  - `sum_diff_from_parameters_Z` (over integers) and `parity_condition_Z`: the same identities specialized to \(\mathbb{Z}\); in particular \(z\pm x\) are even.
  - `no_parameters_if_parity_violation`: rules out integer parameters when observed parity contradicts the necessary evenness.
- **Elementary growth lemmas**
  - `pow2_gt_linear`, `pow3_gt_linear`: exponential vs linear growth.
  - `integer_solution_o`: if \(o>1\) and \(o^n=2\cdot n\) with \(n\ge 1\), then \((o,n)=(2,1)\) or \((2,2)\).
- **Global normalization (this reading)**
  - Section `Normalization_Parameter` introduces a *fixed* \(o\) and an abstract hypothesis  
    `normalization_equation` :
    ```coq
    forall (n x y z : nat),
      2 < n -> x^n + y^n = z^n -> o^n = 2 * n.
    ```
  - Main conditional theorem: `fermat_last_theorem_from_normalization` — under the hypothesis above, FLT holds for all \(n>2\).
  - Convenience corollary `fermat_last_theorem_with_o_two`: if one *chooses* the full-coverage normalization \(o=2\) across all \(n\), then \(2^n=2\cdot n\) follows for any putative counterexample, and the same contradiction results.

**Scope note.** Parity lemmas are provided for completeness but are not needed in the final growth-based contradiction; they document the algebraic consequences of the standard parametrization.

---

## Build & check

```bash
coqc FLT.v
```

- The development compiles without `Admitted`.
- Tested with Coq’s standard libraries (`Arith`, `Lia`, `Reals`, `ZArith`, `Ring`).

---

## Text ↔ Coq map

- Real parametrization: `sum_diff_from_parameters_R`
- Integer parametrization & parity: `sum_diff_from_parameters_Z`, `parity_condition_Z`
- Parity obstruction example: `no_parameters_for_example`
- Growth lemmas: `pow2_gt_linear`, `pow3_gt_linear`
- Only trivial solutions of \(o^n=2\cdot n\): `integer_solution_o`
- Global normalization hypothesis: `normalization_equation` (in section `Normalization_Parameter`)
- FLT from normalization hypothesis: `fermat_last_theorem_from_normalization`
- Corollary with \(o=2\): `fermat_last_theorem_with_o_two`

---

## PDFs

- Russian article (latest) in this repository or: [FLT_Poof_Reconstruction_ru.pdf](https://www.researchgate.net/publication/381293382_OSTRYE_UGLY_V_RASSUZDENII_PERA_FERMA_O_NERAZLOZIMOSTI_STEPENI_VYSE_KVADRATA_OBZOR)  
- English article (latest) in this repository or: [FLT_Poof_Reconstruction_en.pdf](https://doi.org/10.13140/RG.2.2.24342.32321)

---

# FLT-Coq (Русский)

## Главная (условная) формулировка

**Гипотеза глобальной нормировки (аксиома/допущение).**  
Существует фиксированное \(o\in\mathbb{N}\), \(o>1\), такое что для любого \(n>2\) и любой гипотетической натуральной тройки
\[
x^n+y^n=z^n \quad\Longrightarrow\quad o^n=2\cdot n.
\]

**Следствие.**  
Из одного лишь равенства \(o^n=2\cdot n\) элементарно следует \((o,n)\in\{(2,1),(2,2)\}\). Значит, для \(n>2\) решений уравнения Ферма в натуральных числах не существует.

Это утверждение формализовано в Coq как условная теорема. Допущение **не** доказывается в проекте; оно выделено как единственная гипотеза, из которой коротко получается противоречие «в ферматовском стиле».

---

## Что формализовано (Coq)

- **Параметризации над \(\mathbb{R}\) и \(\mathbb{Z}\)**
  - `sum_diff_from_parameters_R`: из \(z:=m^n+p^n\), \(x:=m^n-p^n\) получаем \(z+x=2\,m^n\), \(z-x=2\,p^n\) (над \(\mathbb{R}\)).
  - `sum_diff_from_parameters_Z`, `parity_condition_Z`: те же равенства над \(\mathbb{Z}\); в частности \(z\pm x\) чётны.
  - `no_parameters_if_parity_violation`: исключает целочисленные параметры при несоответствии наблюдаемой чётности необходимой.
- **Элементарные оценки роста**
  - `pow2_gt_linear`, `pow3_gt_linear`: экспонента против линейной функции.
  - `integer_solution_o`: если \(o>1\) и \(o^n=2\cdot n\) (\(n\ge 1\)), то \((o,n)=(2,1)\) или \((2,2)\).
- **Глобальная нормировка (данное прочтение)**
  - В разделе `Normalization_Parameter` вводится фиксированное \(o\) и абстрактная гипотеза  
    `normalization_equation` :
    ```coq
    forall (n x y z : nat),
      2 < n -> x^n + y^n = z^n -> o^n = 2 * n.
    ```
  - Главная условная теорема: `fermat_last_theorem_from_normalization` — при этой гипотезе ВТФ верна для всех \(n>2\).
  - Удобная королларий `fermat_last_theorem_with_o_two`: если *выбрать* нормировку \(o=2\) для всех \(n\), то из любой гипотетической контрпримерной тройки следует \(2^n=2\cdot n\) и получается то же противоречие.

**Замечание о роли чётности.** Леммы о чётности включены для полноты картины следствий стандартной параметризации; в последнем шаге доказательства они не используются — достаточно сравнений роста.

---

## Сборка и проверка

```bash
coqc FLT.v
```

- Компилируется без `Admitted`.
- Используются стандартные библиотеки Coq (`Arith`, `Lia`, `Reals`, `ZArith`, `Ring`).

---

## Соответствие текст ↔ Coq

- Параметризация над \(\mathbb{R}\): `sum_diff_from_parameters_R`
- Параметризация и чётность над \(\mathbb{Z}\): `sum_diff_from_parameters_Z`, `parity_condition_Z`
- Пример препятствия по чётности: `no_parameters_for_example`
- Леммы роста: `pow2_gt_linear`, `pow3_gt_linear`
- Тривиальные решения \(o^n=2\cdot n\): `integer_solution_o`
- Гипотеза глобальной нормировки: `normalization_equation` (в разделе `Normalization_Parameter`)
- ВТФ из гипотезы нормировки: `fermat_last_theorem_from_normalization`
- Королларий при \(o=2\): `fermat_last_theorem_with_o_two`

---

© 2025. Conditional formalization “global normalization ⇒ FLT” (Dedenko reading).