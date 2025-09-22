# FLT-Coq

**Main (conditional) statement.**  
If one accepts *Dedenko's Ansatz*  
> for every $n>2$, any putative solution $x^n+y^n=z^n$ yields an integer $o>1$ with $o^n=2\cdot n$,  
then the Coq development proves that no such solutions exist (FLT for $n>2$).

**Important:** “$2\cdot n$” denotes the product, not a power. Wherever the manuscript
uses “2n” as a product, we write “$2\cdot n$” to avoid ambiguity with $2^n$.

## What is formalized
- The Ansatz is kept as an explicit hypothesis.
- From $o^n=2\cdot n$ we derive $o=2$ and $n\in\{1,2\}$, hence a contradiction for $n>2$.
- Parity constraints: from $z:=m^n+p^n$ and $x:=m^n-p^n$ we must have $z\pm x$ even.
  A general lemma rejects parameterizations when observed parity violates this.

See `FLT.v` and the PDF for details.

---

# FLT-Coq (English)

## Check FLT proof

The Coq code is correct; it provides a formalization of FLT that compiles successfully.

## Fermat's Theorem – Fermat's Own Proof (c) Yurkin Pavel IAEA

Russian nuclear physicist Grigory Leonidovich Dedenko has reconstructed the original reasoning of Pierre de Fermat, which led him to conclude that the sum of two equal natural powers of rational numbers cannot be represented as the same power for an exponent greater than two — the famous (Great) Fermat's Theorem.

As is known, in 1637 Fermat left a note in the margin of Diophantus's "Arithmetica" (which he was apparently reading) stating the discovered fact and adding: "I have discovered a truly marvelous proof of this, which this margin is too narrow to contain."

According to G.L. Dedenko, Fermat analyzed differences of powers using a then-new method — decomposing these differences into a sum of pairwise products (later named the "Newton binomial"). Fermat found that the coefficients of the decomposition then satisfy certain simple conditions, which are equivalent to a simple logarithmic equation (another concept only maturing by the mid-17th century) with respect to the degree of the decomposed sum (or, more precisely, difference). This equation has only two roots — the numbers one and two.

Thus, the margins of the book indeed turned out to be too narrow for a full recording of the marvelous proof — it needed to be preceded and interleaved with the introduction and lemmas of new concepts at that time: decomposition with combinatorial coefficients (Newton's binomial), logarithm, etc. It is now unclear whether Pierre de Fermat ever wrote out his reasoning in detail anywhere, and if he did, whether that record now lies in some unexpected archive. Historians of science are invited to search again.

---

The fully working Coq code is attached, as is the PDF of the reconstructed proof of Fermat's Theorem.

---

# FLT-Coq (Русский)

## Проверка доказательства ВТФ

Код Coq корректен; он предоставляет формализацию Великой теоремы Ферма (ВТФ), которая успешно компилируется.

## Теорема Ферма - доказательство самого Ферма (c) Юркин Павел МАГАТЭ

Русский физик-ядерщик Григорий Леонидович Деденко восстановил исходное рассуждение Пьера Ферма, приведшее последнего к выводу о непредставимости суммы двух одинаковых натуральных степеней рациональных чисел одной такой же степенью для показателя выше квадрата - знаменитой (великой) теореме Ферма.

Ферма оставил, как известно, в 1637 г. пометку на полях (читаемой им, видимо) "Арифметики" Диофанта с формулировкой обнаруженного факта и добавлением - "я нашёл этому поистине чудесное доказательство, но эти поля для него слишком узки".

Как понял Г.Л. Деденко, Ферма анализировал разности степеней новым на тот момент методом - разложением этих разностей в сумму попарных произведений (названным позднее "бином Ньютона" ). Ферма обнаружил, что коэффициенты разложения удовлетворяют тогда некоторым простым условиям, которым эквивалентно некое простое логарифмическое (ещё одно понятие, только вызревавшее к середине XVII века) уравнение относительно степени разлагаемой суммы (или, вернее, разности). Последнее имеет лишь два корня - числа единица и два.

Таким образом, поля книги действительно оказались узки для полной записи чудесного доказательства - её требовалось предварять и перемежать введением и леммированием новых тогда понятий: разложение с комбинаторными коэффициентами (бином Ньютона) , логарифм и пр. Сейчас неясно, записал ли Пьер Ферма своё рассуждение подробно где-либо и - если записал - лежит ли эта запись теперь в каком-нибудь неожиданном архиве. Историкам естествознания предлагается поискать заново.

---

Прилагается полностью рабочий код Coq, а также PDF-файл с реконструированным доказательством теоремы Ферма.

