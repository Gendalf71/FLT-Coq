# FLT-Coq

## Main (conditional) statement
If one accepts *Dedenko’s Ansatz*:
> for every $n>2$, any putative solution $x^n+y^n=z^n$ yields an integer $o>1$ with $o^n=2\cdot n$,

then the Coq development proves that no such solutions exist (FLT for $n>2$).

## Nature of the Ansatz (axiom, not theorem)
The Ansatz is an *axiom*, not a theorem. Its value is not that it can be proved inside elementary number theory, but that --- once assumed --- it forces $o^n=2\cdot n$ and, via the Coq lemmas in this repo, yields Fermat’s Last Theorem for all $n>2$.
This project does **not** prove the Ansatz; it isolates it as a single hypothesis under which a short, elementary, “Fermat-style” proof would follow.

## What is formalized
*   The Ansatz is kept as an explicit hypothesis.
*   From $o^n=2\cdot n$ we derive $o=2$ and $n\in\{1,2\}$, hence a contradiction for $n>2$.
*   Real vs integer parameterizations:
    *   Over **reals** ($m,p\in\mathbb{R}$): `sum_diff_from_parameters_R` yields $z+x=2m^n$ and $z-x=2p^n$.
    *   Over **integers** ($m,p\in\mathbb{Z}$): `sum_diff_from_parameters_Z` and `parity_condition_Z` imply $z\pm x$ are even; a general lemma rejects parameterizations when observed parity violates this.
*   Main theorem under the Ansatz: `fermat_last_theorem_from_ansatz`.

## Build & check
```bash
coqc FLT.v
```

## Code map (text ↔ Coq)
*   Real parametrization: `sum_diff_from_parameters_R`
*   Integer parametrization & parity: `sum_diff_from_parameters_Z`, `parity_condition_Z`
*   Parity obstruction example: `no_parameters_for_example`
*   Growth lemmas: `pow2_gt_linear`, `pow3_gt_linear`
*   Only trivial solutions of $o^n=2\cdot n$: `integer_solution_o`
*   Ansatz (hypothesis): `dedenko_ansatz`
*   FLT from the Ansatz: `fermat_last_theorem_from_ansatz`

---

# Background (English)

## Check FLT proof
The Coq code provides a formalization of the conditional implication “Ansatz ⇒ FLT” and compiles successfully (`coqc FLT.v`).

## Fermat’s Theorem – Fermat’s Own Proof (c) Yurkin Pavel IAEA
Russian nuclear physicist Grigory Leonidovich Dedenko has reconstructed the original reasoning of Pierre de Fermat, which led him to conclude that the sum of two equal natural powers of rational numbers cannot be represented as the same power for an exponent greater than two — the famous (Great) Fermat’s Theorem.

As is known, in 1637 Fermat left a note in the margin of Diophantus’s *Arithmetica* stating the discovered fact and adding: “I have discovered a truly marvelous proof of this, which this margin is too narrow to contain.”

According to G. L. Dedenko, Fermat analyzed differences of powers using a then-new method — the binomial expansion. Fermat found that the coefficients of the expansion satisfy certain simple conditions, which are equivalent to a simple logarithmic equation (another concept only maturing by the mid-17th century) with respect to the degree of the decomposed sum (or, more precisely, difference). This equation has only two roots — $1$ and $2$.

Thus, the margins of the book indeed turned out to be too narrow for a full recording of the marvelous proof — it needed to be preceded and interleaved with the introduction and lemmas of new concepts at that time: binomial coefficients, logarithm, etc. It is now unclear whether Pierre de Fermat ever wrote out his reasoning in detail anywhere, and if he did, whether that record now lies in some unexpected archive. Historians of science are invited to search again.

The fully working Coq code is attached, as is the PDF of the reconstructed proof of Fermat’s Theorem.

---

# FLT-Coq (Русский)

## Что такое Анзац (аксиома, а не теорема)
Анзац — это *аксиома*, а не теорема. Его сила — не в доказуемости, а в том, что из него неизбежно следует равенство $o^n=2\cdot n$ и, как следствие, ВТФ для $n>2$.
Данный проект не доказывает анзац; он выделяет его как единственную гипотезу, при принятии которой получается короткое, элементарное, «ферматово» рассуждение.

## Теорема Ферма — «доказательство самого Ферма» (c) Юркин Павел МАГАТЭ
Русский физик-ядерщик Григорий Леонидович Деденко восстановил исходное рассуждение Пьера Ферма, приведшее его к выводу о непредставимости суммы двух одинаковых натуральных степеней рациональных чисел одной такой же степенью для показателя выше квадрата — знаменитой (великой) теоремы Ферма.

Как известно, в 1637 г. Ферма оставил пометку на полях «Арифметики» Диофанта с формулировкой обнаруженного факта и добавлением: «Я нашёл этому поистине чудесное доказательство, но эти поля для него слишком узки».

По реконструкции Г.Л. Деденко, Ферма анализировал разности степеней методом разложения (впоследствии — «бином Ньютона»). Он обнаружил, что коэффициенты разложения удовлетворяют простым условиям, эквивалентным некоему простому логарифмическому уравнению (ещё одному тогда новому понятию) относительно степени разлагаемой суммы/разности. Это уравнение имеет лишь два корня — $1$ и $2$.

Таким образом, поля книги действительно оказались узки для полной записи «чудесного» доказательства — требовалось предварительное введение и леммирование новых на тот момент идей: комбинаторные коэффициенты, логарифмы и т. п. Неясно, записал ли Ферма рассуждение подробно и сохранилось ли оно. Историкам науки предлагается поискать заново.

**Проверка:** `coqc FLT.v`.
Полностью рабочий код Coq и PDF-файл с реконструкцией прилагаются.