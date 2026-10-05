/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.MarkedXYPartitionedPowerHashing

set_option autoImplicit false

/-!
# The component word of a legal triple, and the two encoding facts it carries

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoSeedInputs.lean`'s bridge
takes a `component : LegalTriple → (Fin (n+1) → C)` together with three facts.  Two of them are
properties of the *encoding* and are proved here, beside the committed
`PartitionHashEncoding.modeledAddress_injOn_legalTargets`.

## The component word

`dwz63ComponentWord H n a` is the source word of the legal triple `a`, read position by position:
`positiveWordEquiv support n (H.sourceWordOfLegalTriple n a)`, valued in the partition support.  In
`[DuanWuZhou2022]`'s notation a position of a large triple carries its level-`ℓ` component
`(i,j,k)`, and that is exactly a supported block address; so the component alphabet is
`C = ↥support` and the `Z`-index of a component is its `Z` leg, `zOf s = (s : BlockAddress A) .Z`.

* `dwz63_componentWord_injOn_legalTargets` — **`hinj`**.  The source word determines the triple on
  any legal-target family (`legalTriple_sourceWordOfLegalTriple_eq_of_mem`), and
  `positiveWordEquiv` is an equivalence, so the component word does too.  This is the same
  round-trip that `modeledAddress_injOn_legalTargets` uses.
* `dwz63_zIndex_eq_of_componentWord` — **`hzHash`**.  The hash's `Z`-word is the field encoding of
  the component word's `Z` leg (`legalTriple`'s own `zIndex` field), so equal `Z`-legs give equal
  hash `Z`-words.

## The third fact is *not* an encoding fact, and not true of the ambient family

`hambient` in `card_dwz63FineCompetitors_le_card_matchableCompatible` asks every competitor to be
**jointly** `α`-typical (`multiplicity (component c) = αType`).  The ambient family of the
asymmetric hashing is only *marginally* typical — that asymmetry is the hash loss
(`Combinatorics/MarkedTwoLegHashingExtraction.lean`'s module doc: `marked = N_α`,
`ambient = N_triple`) — so `hambient` is **false on `ambient`** and holds only on `marked`.

That is not a gap in the argument: a hole needs a *remaining* competitor, and remaining triples are
marked.  `dwz63SplitCompatTyped` therefore carries the joint type as a fourth conjunct of the
relation, and `card_dwz63FineCompetitorsTyped_le_card_matchableCompatible` re-proves the bridge
with `hambient` deleted.  A client instantiating `dwz63_exists_seed_aggregateHoleFraction` at
`dwz63SplitCompatTyped` gets `hcompetitors` with no typicality hypothesis on `ambient` at all.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §2.9 (`hashing.tex`) and §6.2 (`global_value.tex`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor ProgressionHash
open scoped BigOperators

universe u v w

section Encoding

variable {R : Type u} [Field R]
variable {A : Leg → Type v} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {support : Finset (BlockAddress A)}

/-- **The component word of a legal triple**: its source word, read position by position. -/
noncomputable def dwz63ComponentWord (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (a : LegalTriple R (Fin (n + 1)) H.target) : Fin (n + 1) → support :=
  positiveWordEquiv support n (H.sourceWordOfLegalTriple n a)

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- **`hinj`.**  The component word determines the legal triple on any legal-target family. -/
theorem dwz63_componentWord_injOn_legalTargets (H : PartitionHashEncoding (R := R) support)
    (n : ℕ) (words : Finset (PositiveWord support n))
    {x y : LegalTriple R (Fin (n + 1)) H.target}
    (hx : x ∈ H.legalTargets n words) (hy : y ∈ H.legalTargets n words)
    (hxy : dwz63ComponentWord H n x = dwz63ComponentWord H n y) : x = y := by
  have hword : H.sourceWordOfLegalTriple n x = H.sourceWordOfLegalTriple n y :=
    (positiveWordEquiv support n).injective hxy
  calc x = H.legalTriple n (H.sourceWordOfLegalTriple n x) :=
        (H.legalTriple_sourceWordOfLegalTriple_eq_of_mem n words hx).symm
    _ = H.legalTriple n (H.sourceWordOfLegalTriple n y) := by rw [hword]
    _ = y := H.legalTriple_sourceWordOfLegalTriple_eq_of_mem n words hy

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- **The hash's `Z`-word is the encoding of the component word's `Z` leg.** -/
theorem dwz63_zIndex_eq_encode_componentWord (H : PartitionHashEncoding (R := R) support)
    (n : ℕ) (words : Finset (PositiveWord support n))
    {a : LegalTriple R (Fin (n + 1)) H.target} (ha : a ∈ H.legalTargets n words) (i : Fin (n + 1)) :
    a.zIndex i = H.encode .Z ((dwz63ComponentWord H n a i : BlockAddress A) .Z) := by
  conv_lhs => rw [← H.legalTriple_sourceWordOfLegalTriple_eq_of_mem n words ha]
  rfl

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- **`hzHash`.**  Equal component-word `Z` legs give equal hash `Z`-words. -/
theorem dwz63_zIndex_eq_of_componentWord (H : PartitionHashEncoding (R := R) support)
    (n : ℕ) (words : Finset (PositiveWord support n))
    {x y : LegalTriple R (Fin (n + 1)) H.target}
    (hx : x ∈ H.legalTargets n words) (hy : y ∈ H.legalTargets n words)
    (hz : (fun s : support ↦ (s : BlockAddress A) .Z) ∘ dwz63ComponentWord H n x =
      (fun s : support ↦ (s : BlockAddress A) .Z) ∘ dwz63ComponentWord H n y) :
    x.zIndex = y.zIndex := by
  funext i
  rw [dwz63_zIndex_eq_encode_componentWord H n words hx i,
    dwz63_zIndex_eq_encode_componentWord H n words hy i]
  exact congrArg (H.encode .Z) (congrFun hz i)

end Encoding

end AlgebraicComplexity.Examples
