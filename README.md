# FLT-Coq — Two Conditional Routes to FLT via GN(2)

> Coq formalization(s) of a **conditional** route to Fermat’s Last Theorem (FLT) built around the explicit‑base hypothesis **GN(2)**.  
> The shared single assumption in both variants is:
>
> **GN(2).** For any \(n>2\) and any \(x,y,z \in \mathbb{N}\),
>
> \[x^n + y^n = z^n \ \Rightarrow\ 2^n = 2\cdot n.\]
>
> Together with the elementary fact \(2^n > 2\cdot n\) for all \(n \ge 3\), GN(2) gives an immediate contradiction; hence no natural solutions exist for \(n>2\) (FLT). GN(2) is **assumed** (not proved) and is isolated as the single hypothesis.

---

## Repository layout (EN / RU)

This repository contains **two closely related expositions** of the same conditional proof idea:

```
.
├── FLT-new.v            # Coq source (NEW approach)
├── FLT-old.v            # Coq source (OLD approach)
├── *.pdf                # Compiled PDFs in English and Russian (mirrored sets)
├── new/                 # NEW exposition (PDFs, figures; en/ru)
├── old/                 # OLD exposition (PDFs, figures; en/ru)
└── add-once/            # Side-by-side comparison + hypotheses on Fermat’s reasoning (en/ru)
```
- The **root** contains Coq files that compile stand‑alone (`FLT-new.v`, `FLT-old.v`) and the compiled PDFs for quick reading (both EN/RU).
- Subfolders **`old/`** and **`new/`** keep the respective article PDFs (readme/description/proof reconstruction) in **English** and **Russian** versions.
- Folder **`add-once/`** provides a compact comparison of the two approaches and articulates **hypotheses** about Pierre Fermat’s possible line of thought, synthesized from both versions.
- All documents have **bilingual** variants (EN/RU). Exact file names follow the pattern used in the repository (e.g., `*_old_en.pdf`, `*_old_ru.pdf`, `*_en.pdf`, `*_ru.pdf`).

_Notes_: The current README integrates and replaces the earlier summary to reflect the **two‑variant** layout and the **comparison** materials.


## What is formalized (shared core)

- **GN(2) core over \(\mathbb{N}\)**  
  A predicate `GN2` that encodes the hypothesis
  ```coq
  forall (n x y z : nat),
    2 < n ->
    Nat.pow x n + Nat.pow y n = Nat.pow z n ->
    2 ^ n = 2 * n.
  ```
  From `GN2`, the lemma `FLT_from_GN2` derives a contradiction for any putative counterexample with \(n>2\).

- **Elementary growth lemmas**  
  Exponential vs. linear growth (e.g., `2^n > 2·n` for \(n\ge 3\)), and the fact that \(2^n = 2\cdot n\) is possible **only** for \(n \in \{1,2\}\).

- **(Optional) Real “wrapper” and bridge back to \(\mathbb{N}\)**  
  Identities linking \(\mathbb{R}\) and \(\mathbb{N}\) are provided to phrase GN(2) as a coverage statement over reals and then bridge back to naturals. These are **expository** and can be omitted for the core implication.


## OLD vs NEW (expository focus)

Both variants reach the same conditional implication **GN(2) ⇒ FLT**. They differ by exposition and motivation:

- **OLD**: Emphasizes **real parametrization** \(m,p \in \mathbb{R}\) with the identities  
  \(z:=m^n+p^n,\ x:=m^n-p^n \Rightarrow z\pm x = 2\cdot m^n,\,2\cdot p^n\),  
  specialization to \(\mathbb{Z}\) (parity), and consistency checks. These parts **motivate** GN(2) but are **not needed** in the short contradiction once GN(2) is assumed.

- **NEW**: Reframes the motivation around **“full‑coverage normalization at base 2”** and the idea that the **maximal coverage of admissible roots** emerges at the integer normalization \(o=2\). Under this lens, GN(2) codifies the explicit‑base collapse at \(2\), after which the elementary growth lemmas finish the contradiction.  
  (The Coq core remains the same: GN(2) is a hypothesis; the contradiction for \(n>2\) is mechanical.)

- **add-once/**: Presents a **side‑by‑side comparison** and distills working **hypotheses on Fermat’s reasoning**, inferred from the two expositions.


## Build & check

You can compile each variant independently using only the standard library:

```bash
coqc FLT-new.v
coqc FLT-old.v
```
Dependencies: Coq (with `Arith`, `Lia`, `Reals`, `ZArith`, `Ring`). No `Admitted` in the proof scripts.


## Reading guide (bilingual)

- **EN**: `Dedenko_FLT_Coq_README*.pdf`, `FLT_Proof_Reconstruction*.pdf`, `Dedenko_FLT_Description*.pdf` (both **old** and **new** variants live side-by-side).
- **RU**: Russian counterparts for each of the above (same folders).

See `add-once/` for the comparison deck and Fermat hypotheses (EN/RU).


## Scope disclaimer

This project **does not prove GN(2)**. It isolates GN(2) as the **single assumption** under which a short, elementary contradiction to \(x^n + y^n = z^n\) for \(n>2\) follows immediately.


## Acknowledgements

We thank colleagues and prior discussions that inspired both expositions and the comparison notes. A special note of gratitude to **S. P. Klykov** whose materials informed Appendix‑style developments and motivated parts of the “new” framing (normalization viewpoint).

---

# FLT-Coq (Русский)

> Два близких по идее **условных** подхода к Великой теореме Ферма (ВТФ), оба построены вокруг гипотезы **ГН(2)**:
>
> **ГН(2).** Для любого \(n>2\) и любых \(x,y,z \in \mathbb{N}\),
>
> \[x^n + y^n = z^n \ \Rightarrow\ 2^n = 2\cdot n.\]
>
> Вместе с элементарным фактом \(2^n > 2\cdot n\) при всех \(n \ge 3\) это даёт немедленное противоречие; следовательно, решений в \(\mathbb{N}\) при \(n>2\) нет (ВТФ). ГН(2) **не доказывается**, а выделяется как единственное допущение.

### Структура репозитория

- В корне: компилируемые Coq‑файлы **`FLT-new.v`** и **`FLT-old.v`** и соответствующие PDF‑версии (EN/RU).  
- В каталоге **`new/`** — «новая» экспозиция (EN/RU).  
- В каталоге **`old/`** — «старая» экспозиция (EN/RU).  
- В каталоге **`add-once/`** — **сравнение** двух подходов и **гипотезы** о ходе мыслей П. Ферма (EN/RU).

### Сборка

```bash
coqc FLT-new.v
coqc FLT-old.v
```

### Пояснения

- **OLD**: акцент на параметризацию \(m,p \in \mathbb{R}\), переход к \(\mathbb{Z}\) и проверки чётности/согласованности. Это мотивация; финальная импликация из ГН(2) не требует этих разделов.
- **NEW**: акцент на «**нормировке базы 2**» и идее, что **наибольшее покрытие корней** возникает при целочисленной нормировке \(o=2\); далее элементарные оценки роста завершают противоречие.
- **add-once/**: компактная «партитура» сравнения и выводы о возможной логике Ферма.

### Дисклеймер

Проект **не доказывает ГН(2)**, а демонстрирует, как при её принятии ВТФ для \(n>2\) следует немедленно.

---

© 2025. FLT-Coq: Conditional GN(2) ⇒ FLT (two-variant exposition; EN/RU).
