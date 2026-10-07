# Changes to the vendored `OAI` sources

## The all-fields `9/4` modules

Source: `selanavot/matrix-multiplication-all-fields`, `lean/OAI`, commit
`c4aaf797f2a8e631e3bc17347fc1fe627341c16e` (Lean `v4.34.1`, Mathlib `d13f23b7`).
This repository builds with Lean `v4.33.0-rc1` and a Mathlib from 2026-07-16, ten weeks older, so
a few names had to be translated back. No definition or theorem statement was changed; every edit
is in an `import` line or inside a proof.

| Change | Files | Why |
| --- | --- | --- |
| `import Mathlib.Basic.Real.Basic` → `import Mathlib.Data.Real.Basic` | 6 files | module renamed in newer Mathlib |
| `import Mathlib` → five specific imports | `Model.lean` | this repository cannot build all of Mathlib locally; the definitions are byte-identical |
| `ofPred_forall`, `Set.ofPred_forall`, `Set.mem_ofPred_eq` → `setOf_forall`, `Set.setOf_forall`, `Set.mem_setOf_eq` | 4 files | lemma family renamed in newer Mathlib |
| `ite_eq_left h`, `ite_eq_right h` → `if_pos h`, `if_neg h` | 7 files | names introduced after Lean `v4.33` |
| `Nonneg ℝ`, `Nonneg ℚ` → `{c : ℝ // 0 ≤ c}`, `{c : ℚ // 0 ≤ c}` | 3 files | `Nonneg` abbreviation does not exist yet; it unfolds to this subtype |
| `toAntisymmetrization_eq (· ≤ ·) T S` → `Quotient.eq` | `AuxiliarySeparation/Tensor/Semiring.lean` | lemma added in newer Mathlib; it is `Quotient.eq` |
| `Finset.prod_le_prod` → `Finset.prod_le_prod'` on products of natural numbers | `Entropy/ComplexHierarchySeparationRates.lean`, `Separation/ComplexStageHierarchyResources.lean` | in the pinned Mathlib the unprimed lemma is the ordered-semiring one and asks for nonnegativity; the primed one is the ordered-monoid statement used upstream |
| `Finset.prod_le_prod₀` → `Finset.prod_le_prod` | `AuxiliarySeparation/Polynomial/ProductBounds.lean` | same rename, the other direction: the real-valued lemma with nonnegativity hypotheses |
| `convert h using 1 <;> field_simp` → `refine le_of_eq_of_le ?_ (le_of_le_of_eq h ?_) <;> field_simp` | `AuxiliarySeparation/Polynomial/ProductBounds.lean` | the older `convert` leaves an extra instance goal `Real.instLE = _` |

## The rectangular and dual-exponent modules

Source: `openai/math`, `lean/OAI/LinearAlgebra/MatrixMultiplication`, commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a` — the 130 modules that the two theorems
`CW75ReorderedRectangular.rectangularOmega_lt_target` and `DualExponentBound.alpha_gt` import and
that the all-fields fork does not contain. (The other 47 modules they import are in the fork,
unmodified by it, and are the files listed above.) 34 of the 130 files were edited, 128 lines in
all, again only inside proofs or in an `import` line:

| Change | Files | Why |
| --- | --- | --- |
| `ite_eq_left h`, `ite_eq_right h`, `dite_eq_left h`, `dite_eq_right h` → `if_pos h`, `if_neg h`, `dif_pos h`, `dif_neg h` | 29 files | names introduced after Lean `v4.33` |
| `ite_true`, `ite_false` → `if_true`, `if_false` | 7 files in `Duality/` | on Lean `v4.33` `ite_true` is stated for the canonical `Decidable True` instance only and does not fire on the instances these proofs meet; `if_true` is the instance-generic statement |
| `Finset.prod_le_prod` → `Finset.prod_le_prod'` on products of natural numbers | `Separation/ComplexBalancedSeparation.lean`, `Tensor/ComplexExecutionPairingBudget.lean` | as above |
| `fin_cases i <;> norm_num […]` → `… <;> decide` | `Tensor/BaseTensorBudgets.lean` (two proofs) | the older `norm_num` leaves the constructor disequalities `¬Color.B = Color.A ∧ …` open |
| `import Mathlib.Basic.Real.Basic` → `import Mathlib.Data.Real.Basic` | 1 file | as above |

The same applies to `FixedPointTheorems/` (source `harfe/fixed-point-theorems-lean4`, commit
`770940ddf9878cf61952ed53d910b92bca841838`, written for Lean `v4.32.0`):

| Change | Files | Why |
| --- | --- | --- |
| proof hunks of the Lean `v4.34.1` compatibility patch shipped by `openai/math` and by the all-fields fork (`lean/patches/fixed-point-theorems-lean4341.patch`), with that patch's `v4.34`-only syntax (`convert!`, `using!`, `ofPred`) translated back and its `import Mathlib` lines not taken | `cubical_sperner.lean` | three proofs fail on `v4.33` as on `v4.34` |
| `noncomputable` on `coord_change_count` and `ccc_fun`; the patch's proof of `ccc_fun_case_D_iff` | `cubical_sperner_prep.lean` | same patch, the two hunks that are needed |
