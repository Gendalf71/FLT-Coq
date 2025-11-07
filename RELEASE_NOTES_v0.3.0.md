# FLT-Coq v0.3.0 — Release Notes (2025-11-07)

**Highlights**  
- **New module: `GlobalNormalization`** consolidates the “global‑normalization reading” with a clear public API and an aggressively minimized internal surface via `#[local]` declarations.  
- **Public theorems exported** (via `Export GlobalNormalization`):  
  - `covers_with` (def) · `covers_with_one_forces_two`  
  - `two_real_normalizations_imply_nat_power_eq` *(“bridge” lemma)*  
  - `covers_with_two_characterisation` · `maximum_coverage_as_theorem`  
  - `normalization_parameter_is_two` · `normalization_forces_small_exponent`  
  - `fermat_last_theorem_from_global_normalization` · `fermat_last_theorem_via_maximum_coverage`  
- **Minimal p‑adic bracket scaffold** (`Section PadicBracket`): record `OPadic`, predicates `NatOddGreater1`, `padic_equation`, and lemmas `odd_primes_vanish_in_o`, `two_adic_normalisation`.  
- **Sanity goals** at the end of the file (quick regression checks).  
- **House‑keeping**: removed unused imports, tightened scopes (`Local Open Scope %Z/%nat/%R`), and marked helper lemmas `#[local]` to prevent API leakage.

> This version supersedes the structure described in v0.2.0 notes while keeping the same conceptual intent (conditional FLT under a normalization premise). fileciteturn3file0

---

## What changed since v0.2.0
- Introduced **namespaced implementation** in `Module GlobalNormalization` with explicit `Export ...` of the *public* symbols only.  
- Refactored auxiliary facts: binomial‑style divisibility, parity and growth lemmas are now **`#[local]`** and thus internal.  
- Added the **bridge lemma** `two_real_normalizations_imply_nat_power_eq` connecting real‑parameter coverage equalities to a natural‑power equality.  
- Added **p‑adic bracket** mini‑abstraction for documenting the intended normalization of the odd primes vs the 2‑adic component.  
- Embedded **sanity goals** to catch regressions early when editing the file.  
- Trimmed imports (no `Binomial`, `Znumtheory`), clarified `Local Open Scope` usage.

> v0.2.0 highlighted two parallel tracks and CI/tooling foundations. Those foundations remain; this release focuses on the **single, cleaned module** and public API clarity. fileciteturn3file0

---

## File layout (key item)
- `GlobalNormalization.v` — defines the module and exports the public theorems listed above.

If you keep legacy files from earlier snapshots, prefer importing from the new module:
```coq
From Coq Require Import Arith Lia Reals ZArith Ring Lra.
From Coq Require Import Arith.PeanoNat.
Require Import GlobalNormalization.
```
Public symbols can be used unqualified after `Export GlobalNormalization` in the file.

---

## Build & test locally
```bash
# Clean build (if you use a Makefile/.coqproject)
make clean && make

# Or compile the module directly
coqc -Q . "" GlobalNormalization.v
```
The file contains tiny **sanity goals** that should solve automatically; any failure signals a regression.

## Build with Docker
```bash
docker run --rm -v "$PWD":/coq -w /coq coqorg/coq:8.18.0   bash -lc 'coqc -Q . "" GlobalNormalization.v'
```

> CI settings from v0.2.0 remain compatible with this file layout; no `Admitted.` is allowed in the repository.

---

## Breaking changes / migration notes
- Many helper lemmas are now **`#[local]`** and no longer available to downstream code. Replace external uses with the **public** counterparts where applicable (e.g., prefer `covers_with_two_characterisation` instead of directly relying on internal growth facts).  
- If you previously depended on separate “track” files, you can keep them for historical reference; the **recommended entry‑point** is now `GlobalNormalization.v` with the exported API listed above.

---

## Next milestones
- Tag **v0.3.1** to integrate README math rendering improvements (GitHub‑friendly LaTeX inline `$…$`) and refresh badges.  
- Optional: add a small `theories/` split and a public interface file `GlobalNormalizationPublic.v` to make the surface even clearer.  
- Explore compatibility run on Coq 8.19/8.20 (scopes, `Z.of_nat` changes) and add matrix CI.

---

*Changelog authored from the v0.3.0 code snapshot of `GlobalNormalization.v`.*
