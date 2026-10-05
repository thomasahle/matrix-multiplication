/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.HashingProbability
import AlgebraicComplexity.Combinatorics.LegwiseHashingExtraction

/-!
# Conditional independence of the affine hash on a colliding pair of legal triples

Layer 2 (`AlgebraicComplexity/Combinatorics/`).  This module proves

> R. Duan, H. Wu and R. Zhou, *Faster Matrix Multiplication via Asymmetric Hashing*,
> arXiv:2210.10173v5, **§2.9 (`hashing.tex`), `lemma:hash_independence`** (`[DuanWuZhou2022]`),
> attributed there to [CoppersmithWinograd1987].

The lemma has two halves.  For two *distinct* legal triples `(X_I, Y_J, Z_K)` and
`(X_{I'}, Y_{J'}, Z_K)` sharing their Z block,

1. `Pr[h_X(I') = h_Z(K) ∣ h_X(I) = h_Z(K)] = M⁻¹`, and
2. `Pr[h_X(I) = h_X(I') = h_Z(K) = b] = M⁻³` **exactly**, for each fixed bucket `b`;

and the paper adds "Same for triple pairs sharing X or Y-blocks."

## What was already available, and what this module adds

The exact fiber counts underlying both halves are already proved:
`Seed.card_commonBucket_collision_mul` is the division-free `M⁻¹` conditional fiber ratio,
`Seed.card_commonBucket_mul_square` says the common-bucket event removes exactly two field degrees
of freedom, and `Seed.uniformSeed_collision_mass` is their probabilistic image.  Those are the
facts the *isolation* route actually consumes: the extraction theorems of this library replace
`[DuanWuZhou2022]`'s expectation computation by the exact `3/4` union bound
`Seed.three_mul_ncard_commonBucketSeeds_le_four_mul_ncard_isolatedSeeds`, so nothing in
`MarkedTwoLegHashingExtraction.lean` needs a probability at all.

What is genuinely missing, and is supplied here, is the *packaging for a colliding pair of legal
triples*, in particular the shared-Z case the paper states its lemma in:

* `LegalTriple.eq_of_zIndex_eq_of_xIndex_eq` / `…_of_yIndex_eq` — with the Z word fixed, legality
  makes the X and Y words determine each other, so two distinct triples sharing a Z block differ on
  *both* remaining legs.  The paper uses this silently ("`I` determines `J` given `K`").
* `LegalTriple.inCommonTriple_pair_iff_collisionProxy` — the reduction that does the work: for a
  pair sharing *any one* leg, the six hash equations of the two triples are equivalent to the two
  equations of the first triple plus **one** further Y-collision, namely at the existing
  `collisionProxy`.  The three sharing modes need three different reasons (a shared X word makes
  the second X-hash free; a shared Y word makes the second Y-hash free; a shared Z word makes the
  second Z-hash free and the progression identity then transfers X to Y), which is exactly the
  paper's unproved "Same for triple pairs sharing X or Y-blocks".
* `LegalTriple.card_inCommonTriple_pair_mul_cube` — half 2 in division-free form: the seeds putting
  both triples in bucket `b` are exactly a `M⁻³` fraction of the whole seed space.
* `LegalTriple.uniformSeed_inCommonTriple_pair_mass` — half 1, stated multiplicatively as
  `mass(pair) = mass(first triple) / |R|` rather than as a conditional probability, so that no
  conditioning measure has to be introduced.

## Two things the paper waves at, and where they went

`[DuanWuZhou2022]`'s proof argues that `h(I) := h_X(I) − h_Z(K)` "is a pairwise independent
uniform hash function", and then that the event `{h_X(I) = h_X(I') = h_Z(K)}` is measurable with
respect to `(w₀, w)` alone, so that the offset `b₀` shifts it uniformly over the `M` buckets.
Neither step appears here as an obligation: both are already contained in
`Seed.commonBucketEquivWeights`, the exact parametrization of a common-bucket fiber by the free
weight table.  That equivalence says precisely that the offset and shift are *determined* by the
weights and the bucket, which is the uniform-shift argument, while
`FiniteLinearHash.card_dot_fiber_mul` is the pairwise-independence input.  Recording this is the
point of the module: the paper's measurability sentence is not an extra hypothesis but a
consequence of a counting fact already proved.

## Non-goals

No asymptotics, no Salem--Spencer input, and no expectation over the bucket set `B`: those belong
to the extraction and client layers.  The statements here are exact identities for one fixed
bucket.
-/

namespace AlgebraicComplexity

universe u v

namespace ProgressionHash

namespace Seed

variable {R : Type u} [Field R]
variable {ι : Type v} [Fintype ι]

/-- Mirror of `zHash_eq_of_commonBucket`: for a legal block triple whose X- and Z-hashes are both
`b`, the Y-hash is `b` as well.

Proof sketch: the three hashes of a legal triple form a three-term arithmetic progression
`h_X + h_Y = 2 h_Z`; substituting `h_X = h_Z = b` and cancelling gives `h_Y = b`. -/
theorem yHash_eq_of_xHash_eq_of_zHash_eq [NeZero (2 : R)]
    (seed : Seed R ι) (I J K : ι → R) (target b : R)
    (hlegal : ∀ t, I t + J t + K t = target)
    (hx : seed.xHash I = b) (hz : seed.zHash target K = b) :
    seed.yHash J = b := by
  have hp := hash_progression seed.offset seed.shift target seed.weights I J K hlegal
  rw [← xHash, ← yHash, ← zHash, hx, hz] at hp
  exact add_left_cancel hp

end Seed

namespace LegalTriple

variable {R : Type u} [Field R]
variable {ι : Type v} [Fintype ι]
variable {target : R}

/-! ### Legality forces the two non-shared legs apart -/

omit [Fintype ι] in
/-- With the Z word fixed, the X word determines the Y word.  Hence two legal triples sharing both
their Z and their X blocks are equal. -/
theorem eq_of_zIndex_eq_of_xIndex_eq {left right : LegalTriple R ι target}
    (hz : left.zIndex = right.zIndex) (hx : left.xIndex = right.xIndex) :
    left = right := by
  refine eq_of_xIndex_eq_yIndex_eq hx ?_
  funext i
  have hleft := left.legal i
  have hright := right.legal i
  rw [congrFun hx i, congrFun hz i] at hleft
  linear_combination hleft - hright

omit [Fintype ι] in
/-- With the Z word fixed, the Y word determines the X word.  Hence two legal triples sharing both
their Z and their Y blocks are equal. -/
theorem eq_of_zIndex_eq_of_yIndex_eq {left right : LegalTriple R ι target}
    (hz : left.zIndex = right.zIndex) (hy : left.yIndex = right.yIndex) :
    left = right := by
  refine eq_of_xIndex_eq_yIndex_eq ?_ hy
  funext i
  have hleft := left.legal i
  have hright := right.legal i
  rw [congrFun hy i, congrFun hz i] at hleft
  linear_combination hleft - hright

omit [Fintype ι] in
/-- **`[DuanWuZhou2022]`'s silent step.**  Two distinct legal triples sharing a Z block differ on
both remaining legs.  The paper phrases this as "`I` determines `J` given `K`". -/
theorem xIndex_ne_and_yIndex_ne_of_zIndex_eq {left right : LegalTriple R ι target}
    (hz : left.zIndex = right.zIndex) (hne : left ≠ right) :
    left.xIndex ≠ right.xIndex ∧ left.yIndex ≠ right.yIndex :=
  ⟨fun hx => hne (eq_of_zIndex_eq_of_xIndex_eq hz hx),
    fun hy => hne (eq_of_zIndex_eq_of_yIndex_eq hz hy)⟩

/-! ### The pair event is one extra collision -/

/-- **The reduction behind `lemma:hash_independence`.**  Let `left` and `right` be legal triples
sharing their block word on some leg.  Then the six hash equations saying that *both* triples sit
in bucket `b` are equivalent to the two equations placing `left` in bucket `b`, together with the
single further equation `h_Y(collisionProxy left right) = b`.

Distinctness of the two triples is deliberately *not* assumed: it is needed only to know that the
proxy is a genuine competitor (`collisionProxy_ne`), which is where the counting consequences below
use it.

Proof sketch.  The forward direction needs no sharing hypothesis: on the common-bucket fiber of
`left`, `Seed.yHash_transportXAlternative_eq_xHash` turns the transported proxy back into
`h_X(right)`, and the untransported proxy is `right`'s own Y word.  The converse is where the
three sharing modes differ.  A shared X word makes `h_X(right) = b` automatic and the proxy is
`right`'s Y word; a shared Y word makes `h_Y(right) = b` automatic while the proxy supplies
`h_X(right) = b`; a shared Z word makes `h_Z(right) = h_Z(left) = b` automatic, and the
progression identity `h_X + h_Y = 2 h_Z` then upgrades the proxy's `h_X(right) = b` to
`h_Y(right) = b`.  That third case is the one `[DuanWuZhou2022]` state the lemma in; the first two
are their "Same for triple pairs sharing X or Y-blocks". -/
theorem inCommonTriple_pair_iff_collisionProxy [NeZero (2 : R)]
    {left right : LegalTriple R ι target}
    {leg : Tensor.Leg} (hleg : right.legIndex leg = left.legIndex leg)
    (b : R) (seed : Seed R ι) :
    (Seed.InCommonTriple left.xIndex left.yIndex left.zIndex target b seed ∧
        Seed.InCommonTriple right.xIndex right.yIndex right.zIndex target b seed) ↔
      (Seed.InCommonBucket left.xIndex left.yIndex b seed ∧
        seed.yHash (collisionProxy left right) = b) := by
  classical
  rw [Seed.inCommonTriple_iff_commonBucket seed left.xIndex left.yIndex left.zIndex target b
      left.legal,
    Seed.inCommonTriple_iff_commonBucket seed right.xIndex right.yIndex right.zIndex target b
      right.legal]
  constructor
  · rintro ⟨hleft, hright⟩
    refine ⟨hleft, ?_⟩
    unfold collisionProxy
    split_ifs with hx
    · exact hright.2
    · rw [Seed.yHash_transportXAlternative_eq_xHash seed left.xIndex left.yIndex
        right.xIndex b hleft]
      exact hright.1
  · rintro ⟨hleft, hproxy⟩
    refine ⟨hleft, ?_⟩
    unfold collisionProxy at hproxy
    split_ifs at hproxy with hx
    · -- The two triples share their X word, so only the Y equation is new.
      exact ⟨by rw [hx]; exact hleft.1, hproxy⟩
    · -- Otherwise the proxy is the transported X word, giving `h_X(right) = b` directly.
      have hxRight : seed.xHash right.xIndex = b := by
        rw [← Seed.yHash_transportXAlternative_eq_xHash seed left.xIndex left.yIndex
          right.xIndex b hleft]
        exact hproxy
      refine ⟨hxRight, ?_⟩
      cases leg with
      | X => exact absurd hleg hx
      | Y =>
          rw [LegalTriple.legIndex_Y, LegalTriple.legIndex_Y] at hleg
          rw [hleg]
          exact hleft.2
      | Z =>
          rw [LegalTriple.legIndex_Z, LegalTriple.legIndex_Z] at hleg
          have hzLeft : seed.zHash target left.zIndex = b :=
            Seed.zHash_eq_of_commonBucket seed left.xIndex left.yIndex left.zIndex target b
              left.legal hleft
          have hzRight : seed.zHash target right.zIndex = b := by
            rw [hleg]; exact hzLeft
          exact Seed.yHash_eq_of_xHash_eq_of_zHash_eq seed right.xIndex right.yIndex
            right.zIndex target b right.legal hxRight hzRight

/-- Set form of `inCommonTriple_pair_iff_collisionProxy`. -/
theorem inCommonTriple_pair_set_eq [NeZero (2 : R)]
    {left right : LegalTriple R ι target}
    {leg : Tensor.Leg} (hleg : right.legIndex leg = left.legIndex leg) (b : R) :
    {seed : Seed R ι |
        Seed.InCommonTriple left.xIndex left.yIndex left.zIndex target b seed ∧
          Seed.InCommonTriple right.xIndex right.yIndex right.zIndex target b seed} =
      {seed : Seed R ι | Seed.InCommonBucket left.xIndex left.yIndex b seed ∧
        seed.yHash (collisionProxy left right) = b} :=
  Set.ext fun seed => inCommonTriple_pair_iff_collisionProxy hleg b seed

/-! ### The two halves of `lemma:hash_independence` -/

/-- **Half 2, in exact division-free form.**  For two distinct legal triples sharing a block word
on some leg, the seeds putting *both* triples into a fixed bucket `b` occupy exactly a `|R|⁻³`
fraction of the seed space:

`#{seeds hashing both triples to b} · |R|³ = #{seeds}`.

This is `[DuanWuZhou2022]`'s "the probability that `h_X(I) = h_X(I') = h_Z(K) = b` … is exactly
`M⁻³`", with no division and no probability measure.

Proof sketch: `inCommonTriple_pair_iff_collisionProxy` identifies the pair event with one
common-bucket event plus one Y-collision; `Seed.card_commonBucket_collision_mul` contributes the
first factor `|R|` and `Seed.card_commonBucket_mul_square` the remaining `|R|²`. -/
theorem card_inCommonTriple_pair_mul_cube [Fintype R] [NeZero (2 : R)]
    {left right : LegalTriple R ι target} (hne : right ≠ left)
    {leg : Tensor.Leg} (hleg : right.legIndex leg = left.legIndex leg) (b : R) :
    Nat.card {seed : Seed R ι //
          Seed.InCommonTriple left.xIndex left.yIndex left.zIndex target b seed ∧
            Seed.InCommonTriple right.xIndex right.yIndex right.zIndex target b seed} *
        (Fintype.card R * Fintype.card R * Fintype.card R) =
      Fintype.card (Seed R ι) := by
  classical
  have hcongr :
      Nat.card {seed : Seed R ι //
          Seed.InCommonTriple left.xIndex left.yIndex left.zIndex target b seed ∧
            Seed.InCommonTriple right.xIndex right.yIndex right.zIndex target b seed} =
        Nat.card {seed : Seed R ι //
          Seed.InCommonBucket left.xIndex left.yIndex b seed ∧
            seed.yHash (collisionProxy left right) = b} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun seed =>
      inCommonTriple_pair_iff_collisionProxy hleg b seed)
  have hcollision := Seed.card_commonBucket_collision_mul left.xIndex left.yIndex
    (collisionProxy left right) b (collisionProxy_ne left right hne)
  rw [Nat.card_eq_fintype_card (α := R)] at hcollision
  have hbase := Seed.card_commonBucket_mul_square (R := R) (ι := ι) left.xIndex left.yIndex b
  rw [hcongr]
  calc
    Nat.card {seed : Seed R ι //
          Seed.InCommonBucket left.xIndex left.yIndex b seed ∧
            seed.yHash (collisionProxy left right) = b} *
          (Fintype.card R * Fintype.card R * Fintype.card R) =
        Nat.card {seed : Seed R ι //
            Seed.InCommonBucket left.xIndex left.yIndex b seed ∧
              seed.yHash (collisionProxy left right) = b} * Fintype.card R *
          (Fintype.card R * Fintype.card R) := by ring
    _ = Nat.card {seed : Seed R ι // Seed.InCommonBucket left.xIndex left.yIndex b seed} *
          (Fintype.card R * Fintype.card R) := by rw [hcollision]
    _ = Fintype.card (Seed R ι) := hbase

/-- **Half 1, in multiplicative form.**  Under a uniform affine seed, the mass of the event that
two distinct legal triples sharing a leg *both* land in bucket `b` is the mass of the first
triple's event divided by `|R|`.

This is `[DuanWuZhou2022]`'s `Pr[h_X(I') = h_Z(K) ∣ h_X(I) = h_Z(K)] = M⁻¹` without introducing a
conditional measure: the ratio is stated directly between the joint and the base mass. -/
theorem uniformSeed_inCommonTriple_pair_mass [Fintype R] [NeZero (2 : R)]
    {left right : LegalTriple R ι target} (hne : right ≠ left)
    {leg : Tensor.Leg} (hleg : right.legIndex leg = left.legIndex leg) (b : R) :
    (uniformSeed R ι).toOuterMeasure
        {seed : Seed R ι |
          Seed.InCommonTriple left.xIndex left.yIndex left.zIndex target b seed ∧
            Seed.InCommonTriple right.xIndex right.yIndex right.zIndex target b seed} =
      (uniformSeed R ι).toOuterMeasure
          {seed : Seed R ι |
            Seed.InCommonTriple left.xIndex left.yIndex left.zIndex target b seed} /
        Fintype.card R := by
  have hbase :
      {seed : Seed R ι |
          Seed.InCommonTriple left.xIndex left.yIndex left.zIndex target b seed} =
        {seed : Seed R ι | Seed.InCommonBucket left.xIndex left.yIndex b seed} :=
    Set.ext fun seed =>
      Seed.inCommonTriple_iff_commonBucket seed left.xIndex left.yIndex left.zIndex target b
        left.legal
  rw [inCommonTriple_pair_set_eq hleg b, hbase]
  exact Seed.uniformSeed_collision_mass left.xIndex left.yIndex
    (collisionProxy left right) b (collisionProxy_ne left right hne)

/-! ### The paper's shared-Z statement

The specializations below are the literal reading of `lemma:hash_independence`, kept so that a
reader checking the source against the library does not have to supply the leg themselves.  They
are exactly the asymmetric-hashing case: `[DuanWuZhou2022]` deliberately allow a Z block to serve
many triples, so a shared-Z pair is the configuration whose probability has to be controlled. -/

/-- `lemma:hash_independence`, half 2, for the paper's shared-Z pair. -/
theorem card_inCommonTriple_sharedZ_mul_cube [Fintype R] [NeZero (2 : R)]
    {left right : LegalTriple R ι target} (hne : right ≠ left)
    (hz : right.zIndex = left.zIndex) (b : R) :
    Nat.card {seed : Seed R ι //
          Seed.InCommonTriple left.xIndex left.yIndex left.zIndex target b seed ∧
            Seed.InCommonTriple right.xIndex right.yIndex right.zIndex target b seed} *
        (Fintype.card R * Fintype.card R * Fintype.card R) =
      Fintype.card (Seed R ι) :=
  card_inCommonTriple_pair_mul_cube hne (leg := Tensor.Leg.Z) hz b

/-- `lemma:hash_independence`, half 1, for the paper's shared-Z pair. -/
theorem uniformSeed_inCommonTriple_sharedZ_mass [Fintype R] [NeZero (2 : R)]
    {left right : LegalTriple R ι target} (hne : right ≠ left)
    (hz : right.zIndex = left.zIndex) (b : R) :
    (uniformSeed R ι).toOuterMeasure
        {seed : Seed R ι |
          Seed.InCommonTriple left.xIndex left.yIndex left.zIndex target b seed ∧
            Seed.InCommonTriple right.xIndex right.yIndex right.zIndex target b seed} =
      (uniformSeed R ι).toOuterMeasure
          {seed : Seed R ι |
            Seed.InCommonTriple left.xIndex left.yIndex left.zIndex target b seed} /
        Fintype.card R :=
  uniformSeed_inCommonTriple_pair_mass hne (leg := Tensor.Leg.Z) hz b

end LegalTriple

end ProgressionHash

end AlgebraicComplexity
