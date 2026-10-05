/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainHoleBudget
import AlgebraicComplexity.MatrixMultiplication.PartitionedSymmetrizedHashing

set_option autoImplicit false

/-!
# The batching that satisfies the stage's `hbatch` and `hbudget`

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoLocalizedStage.lean`'s
`dwz63_localizedGroupedStage_of_segmentedRepair` takes `batch`, `hbatch` and `hbudget` as
parameters.  At `batch := id` they are unsatisfiable with nonempty holes: each fibre is a
singleton, so `hbudget` reads `|avail| · |holes a| < |avail|`, forcing `holes a = ∅`.  The Hole
Lemma repairs **one leaf per batch**, and `[DuanWuZhou2022]` therefore batch `k` retained triples
together with `k` of order `log|avail| / log 8` (`hole_lemma.tex:277`).

**The batching is `uniformBatch`** (`MatrixMultiplication/PartitionedSymmetrizedHashing.lean:297`),
already committed and already carrying the two facts a batch index has to have:
`uniformBatch_surjective` is `hbatch`, and `le_card_uniformBatch_fiber` says every batch holds at
least `k` copies, which is `hcopies`.  Its index type is `Fin batches`, so `β := Fin batches` and
`#β = batches`.

## The parameters, and what they cost

Fix `L` with `|avail| ≤ 2 ^ L` --- `L` is the bit length of the available-word count, so `L = O(n)`
--- and take

`k := ⌈8 (L+1) / 7⌉`,  `batches := #retained / k`.

Then `hfit : batches · k ≤ #retained` holds by construction, `hcopies : 8(L+1) ≤ 7k` holds by the
choice of `k`, and `dwz63_hbudget_uniformBatch` discharges `hbudget` from the `1/8` hole bound
alone.  The price is the copy count: the endpoint now sees `batches` leaves rather than
`#retained`, and `dwz63_card_le_two_mul_mul_div` bounds the loss by `2k`, i.e. by `O(n)` --- the
`1/(8(nℓ+2))` of `hole_lemma.tex:277`, which is polynomial and hence subexponential.  That is the
factor `Examples/DuanWuZhouLevelTwoPlainBatchedEndpoint.lean` feeds through `loss`.

Nothing here needs the `1/8` hole bound itself; it is carried as `hholes` and is still the residual
recorded in `Examples/DuanWuZhouLevelTwoPlainHoleBudget.lean`'s `Dwz63HoleFractionInputs`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6 and `hole_lemma.tex`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u

/-! ## The batching loss is at most `2 k` -/

/-- **Batching into `⌊N / k⌋` batches of size about `k` loses at most a factor `2 k`.**

With `batches = N / k` and `k ≤ N`, one has `N ≤ 2 k · batches`.  This is the whole cost of the
Hole Lemma's batching on the copy count. -/
theorem dwz63_card_le_two_mul_mul_div {N k : ℕ} (hk : 0 < k) (hkN : k ≤ N) :
    N ≤ 2 * k * (N / k) := by
  have hone : 1 ≤ N / k := (Nat.one_le_div_iff hk).mpr hkN
  have hdm := Nat.div_add_mod N k
  have hmod : N % k < k := Nat.mod_lt _ hk
  have hkle : k ≤ k * (N / k) := Nat.le_mul_of_pos_right k (by omega)
  have hassoc : 2 * k * (N / k) = k * (N / k) + k * (N / k) := by ring
  omega

/-! ## `hbudget` at `uniformBatch` -/

section UniformBatch

variable {I : Type u} [Fintype I] [DecidableEq I] {n m : ℕ}
variable {τ : Type} [Fintype τ] [DecidableEq τ]

omit [Fintype τ] in
/-- **`hbudget` for the uniform batching**, in the binder
`dwz63_localizedGroupedStage_of_segmentedRepair` carries it.

`hcopies` is discharged from `le_card_uniformBatch_fiber`; what remains is exactly the `1/8` hole
bound `hholes`, which is `Dwz63HoleFractionInputs`. -/
theorem dwz63_hbudget_uniformBatch (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ)
    (retained : Finset τ)
    (compatibleWith usefulFor : SegmentedAvailableWord seg α → τ → Prop) (L : ℕ)
    (hpos : 0 < Fintype.card (SegmentedAvailableWord seg α))
    (hbound : Fintype.card (SegmentedAvailableWord seg α) ≤ 2 ^ L)
    (hholes : ∀ a : τ, 8 * (dwz63HoleSet seg α retained compatibleWith usefulFor a).card ≤
      Fintype.card (SegmentedAvailableWord seg α))
    {k batches : ℕ} (hk : 0 < k) (hbatches : 0 < batches)
    (hfit : batches * k ≤ Fintype.card retained)
    (hcopies : 8 * (L + 1) ≤ 7 * k) :
    ∀ b : Fin batches,
      Fintype.card (SegmentedAvailableWord seg α) *
          ∏ a : {a : retained // uniformBatch k hbatches a = b},
            (dwz63HoleSet seg α retained compatibleWith usefulFor a.1.1).card <
        Fintype.card (SegmentedAvailableWord seg α) ^
          Fintype.card {a : retained // uniformBatch k hbatches a = b} :=
  dwz63_hbudget_of_holeBound seg α retained compatibleWith usefulFor L hpos hbound hholes
    (uniformBatch k hbatches)
    (fun b ↦ hcopies.trans
      (Nat.mul_le_mul_left 7 (le_card_uniformBatch_fiber hk hbatches hfit b)))

omit [Fintype τ] [DecidableEq τ] in
/-- **`hbatch` for the uniform batching.**  `uniformBatch_surjective`, in the stage's binder. -/
theorem dwz63_hbatch_uniformBatch (retained : Finset τ) {k batches : ℕ}
    (hk : 0 < k) (hbatches : 0 < batches)
    (hfit : batches * k ≤ Fintype.card retained) :
    Function.Surjective (uniformBatch (ι := retained) k hbatches) :=
  uniformBatch_surjective hk hbatches hfit

end UniformBatch

end AlgebraicComplexity.Examples
