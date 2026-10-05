/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.IteratedProduct
import AlgebraicComplexity.Tensor.PartitionedBlockMap
import AlgebraicComplexity.Tensor.PartitionedPowerConstituent

set_option autoImplicit false

/-!
# Blockwise maps through positive partitioned powers

Layer 1 (`AlgebraicComplexity/Tensor/`).  `Tensor.Restricts.partitionedBlockMap`
(`Tensor/PartitionedBlockMap.lean`) compares two partitioned tensors over different block alphabets
through a block dictionary.  This module lifts that data to every positive power: the dictionary
becomes `positiveWordMap (dict c) n` letter by letter, the block maps become their iterated tensor
products, and the letter-level constituent identity, support image and injectivity each propagate
by induction on the exponent.

## Why the letter identity is re-derived in unembedded form

`Restricts.partitionedBlockMap` takes its constituent hypothesis *after* embedding both sides into
the ambient spaces, because that is the only address-free form a client can rewrite in.  The
induction here needs the unembedded form instead, since a successor power is an external product of
constituents and `Tensor.map_external` acts on those directly.  The two are equivalent:
`map_blockInclude_injective` says a block inclusion is a legwise split injection, so embedding
loses nothing, and `map_partitionedBlockMap_constituent` converts.  Clients therefore prove the
easy (embedded) form once and use either.

Primary source: none; this is partitioned-tensor infrastructure.
-/

namespace AlgebraicComplexity.Tensor

open scoped DirectSum

universe u v w

section BlockMapPower

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {B : Leg → Type w} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {W : ∀ c, B c → Type (max u v)}
variable [∀ c b, AddCommMonoid (W c b)] [∀ c b, Module K (W c b)]

/-! ## Two readings of a successor power -/

/-- Membership in a successor positive power is membership of the prefix and the last letter.
Stated in the power's own alphabet, where `mem_external_support`'s pattern does not match. -/
theorem mem_positivePower_succ_support
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ)
    (s : BlockAddress (fun c ↦ PositiveWord (A c) (n + 1))) :
    s ∈ (P.positivePower (n + 1)).support ↔
      (fun c ↦ (s c).1) ∈ (P.positivePower n).support ∧
        (fun c ↦ (s c).2) ∈ P.support :=
  PartitionedTensor.mem_external_support (P.positivePower n) P s

/-- A successor constituent is the external product of the prefix constituent with the letter
constituent. -/
theorem positivePower_succ_constituent
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ)
    (s : BlockAddress (fun c ↦ PositiveWord (A c) (n + 1))) :
    (P.positivePower (n + 1)).constituent s =
      Tensor.external ((P.positivePower n).constituent (fun c ↦ (s c).1))
        (P.constituent (fun c ↦ (s c).2)) := rfl

/-! ## Embedding a constituent loses nothing -/

omit [∀ c, Fintype (A c)] in
/-- Block inclusions are legwise split injections: `DirectSum.component` at the same address is a
retraction, and legwise retractions give a retraction of the induced tensor map. -/
theorem map_blockInclude_injective (s : BlockAddress A) :
    Function.Injective (map (blockInclude (K := K) (V := V) s)) := by
  classical
  have hretract : (fun c ↦ (DirectSum.component K (A c) (V c) (s c)).comp
      (blockInclude (K := K) (V := V) s c)) = fun c ↦ LinearMap.id := by
    funext c
    ext x
    simp [blockInclude]
  have hid : ∀ T : Tensor3 K (fun c ↦ V c (s c)),
      map (fun c ↦ DirectSum.component K (A c) (V c) (s c))
          (map (blockInclude (K := K) (V := V) s) T) = T := by
    intro T
    rw [map_map_comp, hretract]
    exact LinearMap.congr_fun map_id T
  intro X Y hXY
  rw [← hid X, hXY, hid Y]

/-- The unembedded form of the constituent hypothesis of `Restricts.partitionedBlockMap`. -/
theorem map_partitionedBlockMap_constituent
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W)
    (dict : ∀ c, A c → B c)
    (φ : ∀ c a, V c a →ₗ[K] W c (dict c a))
    (s : BlockAddress A)
    (h : map (partitionedBlockMap (K := K) (V := V) (W := W) dict φ)
          (map (blockInclude (K := K) (V := V) s) (P.constituent s)) =
        map (blockInclude (K := K) (V := W) (fun c ↦ dict c (s c)))
          (Q.constituent (fun c ↦ dict c (s c)))) :
    map (fun c ↦ φ c (s c)) (P.constituent s) = Q.constituent (fun c ↦ dict c (s c)) := by
  refine map_blockInclude_injective (K := K) (V := W) (fun c ↦ dict c (s c)) ?_
  rw [← map_partitionedBlockMap_block]
  exact h

/-! ## The word-level blockwise map -/

/-- **The blockwise map of a positive power.**  At a word of source blocks it is the iterated
tensor product of the letterwise block maps, landing in the block named by the letterwise image
word. -/
noncomputable def positiveWordBlockMap (dict : ∀ c, A c → B c)
    (φ : ∀ c a, V c a →ₗ[K] W c (dict c a)) :
    (n : ℕ) → ∀ (c : Leg) (word : PositiveWord (A c) n),
      PositivePowerBlockSpace K V n c word →ₗ[K]
        PositivePowerBlockSpace K W n c (positiveWordMap (dict c) n word)
  | 0, c, word => φ c word
  | n + 1, c, word =>
      TensorProduct.map (positiveWordBlockMap dict φ n c word.1) (φ c word.2)

/-! ## The three hypotheses, lifted -/

/-- The letterwise constituent identity propagates to every positive power.

Proof sketch: induction on the exponent.  A successor constituent is an external product of the
preceding power's constituent with a letter constituent, the word block map is the corresponding
tensor product, and `Tensor.map_external` turns one into the other. -/
theorem map_positiveWordBlockMap_constituent
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W)
    (dict : ∀ c, A c → B c)
    (φ : ∀ c a, V c a →ₗ[K] W c (dict c a))
    (hconstituent : ∀ s ∈ P.support,
      map (fun c ↦ φ c (s c)) (P.constituent s) = Q.constituent (fun c ↦ dict c (s c))) :
    ∀ (n : ℕ) (s : BlockAddress (fun c ↦ PositiveWord (A c) n)),
      s ∈ (P.positivePower n).support →
      map (fun c ↦ positiveWordBlockMap (K := K) (V := V) (W := W) dict φ n c (s c))
          ((P.positivePower n).constituent s) =
        (Q.positivePower n).constituent (fun c ↦ positiveWordMap (dict c) n (s c))
  | 0, s, hs => hconstituent s hs
  | n + 1, s, hs => by
      obtain ⟨hleft, hright⟩ := (mem_positivePower_succ_support P n s).mp hs
      rw [positivePower_succ_constituent]
      show map (fun c ↦ TensorProduct.map
            (positiveWordBlockMap (K := K) (V := V) (W := W) dict φ n c (s c).1)
            (φ c (s c).2))
          (Tensor.external ((P.positivePower n).constituent (fun c ↦ (s c).1))
            (P.constituent (fun c ↦ (s c).2))) = _
      rw [map_external,
        map_positiveWordBlockMap_constituent P Q dict φ hconstituent n
          (fun c ↦ (s c).1) hleft,
        hconstituent (fun c ↦ (s c).2) hright]
      rfl

/-- The letterwise support image propagates to every positive power. -/
theorem positivePower_support_image
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W)
    (dict : ∀ c, A c → B c)
    (hsupport : Q.support = P.support.image (fun s ↦ (fun c ↦ dict c (s c))))
    (hinj : ∀ s ∈ P.support, ∀ t ∈ P.support,
      (fun c ↦ dict c (s c)) = (fun c ↦ dict c (t c)) → s = t) :
    ∀ n : ℕ, (Q.positivePower n).support =
      (P.positivePower n).support.image
        (fun s ↦ (fun c ↦ positiveWordMap (dict c) n (s c)))
  | 0 => hsupport
  | n + 1 => by
      classical
      ext t
      rw [mem_positivePower_succ_support, Finset.mem_image]
      constructor
      · rintro ⟨hleft, hright⟩
        rw [positivePower_support_image P Q dict hsupport hinj n, Finset.mem_image] at hleft
        rw [hsupport, Finset.mem_image] at hright
        obtain ⟨u, hu, hueq⟩ := hleft
        obtain ⟨a, ha, haeq⟩ := hright
        refine ⟨fun c ↦ (u c, a c), ?_, ?_⟩
        · exact (mem_positivePower_succ_support P n _).mpr ⟨hu, ha⟩
        · funext c
          have h1 := congrFun hueq c
          have h2 := congrFun haeq c
          exact Prod.ext h1 h2
      · rintro ⟨u, hu, rfl⟩
        obtain ⟨huleft, huright⟩ := (mem_positivePower_succ_support P n u).mp hu
        constructor
        · rw [positivePower_support_image P Q dict hsupport hinj n, Finset.mem_image]
          exact ⟨fun c ↦ (u c).1, huleft, rfl⟩
        · rw [hsupport, Finset.mem_image]
          exact ⟨fun c ↦ (u c).2, huright, rfl⟩

omit [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
/-- The letterwise injectivity on the support propagates to every positive power. -/
theorem positiveWordMap_injOn_support
    (P : PartitionedTensor (K := K) (A := A) V)
    (dict : ∀ c, A c → B c)
    (hinj : ∀ s ∈ P.support, ∀ t ∈ P.support,
      (fun c ↦ dict c (s c)) = (fun c ↦ dict c (t c)) → s = t) :
    ∀ (n : ℕ), ∀ s ∈ (P.positivePower n).support, ∀ t ∈ (P.positivePower n).support,
      (fun c ↦ positiveWordMap (dict c) n (s c)) =
        (fun c ↦ positiveWordMap (dict c) n (t c)) → s = t
  | 0, s, hs, t, ht, h => hinj s hs t ht h
  | n + 1, s, hs, t, ht, h => by
      rw [mem_positivePower_succ_support] at hs ht
      have hfst : (fun c ↦ positiveWordMap (dict c) n (s c).1) =
          (fun c ↦ positiveWordMap (dict c) n (t c).1) := by
        funext c
        exact congrArg Prod.fst (congrFun h c)
      have hsnd : (fun c ↦ dict c (s c).2) = (fun c ↦ dict c (t c).2) := by
        funext c
        exact congrArg Prod.snd (congrFun h c)
      have h1 := positiveWordMap_injOn_support P dict hinj n
        (fun c ↦ (s c).1) hs.1 (fun c ↦ (t c).1) ht.1 hfst
      have h2 := hinj (fun c ↦ (s c).2) hs.2 (fun c ↦ (t c).2) ht.2 hsnd
      funext c
      exact Prod.ext (congrFun h1 c) (congrFun h2 c)

/-! ## The packaged restriction -/

/-- **A blockwise map along a block dictionary restricts every positive power.**

The hypotheses are the letter-level ones of `Restricts.partitionedBlockMap`, with the constituent
identity in its embedded form; the conclusion is the same statement one exponent up, with the
dictionary applied letter by letter. -/
theorem Restricts.partitionedBlockMap_positivePower
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W)
    (dict : ∀ c, A c → B c)
    (φ : ∀ c a, V c a →ₗ[K] W c (dict c a))
    (hinj : ∀ s ∈ P.support, ∀ t ∈ P.support,
      (fun c ↦ dict c (s c)) = (fun c ↦ dict c (t c)) → s = t)
    (hsupport : Q.support = P.support.image (fun s ↦ (fun c ↦ dict c (s c))))
    (hconstituent : ∀ s ∈ P.support, ∀ t : BlockAddress B,
      (fun c ↦ dict c (s c)) = t →
      map (AlgebraicComplexity.Tensor.partitionedBlockMap (K := K) (V := V) (W := W) dict φ)
          (map (blockInclude (K := K) (V := V) s) (P.constituent s)) =
        map (blockInclude (K := K) (V := W) t) (Q.constituent t))
    (n : ℕ) :
    Restricts (P.positivePower n).realize (Q.positivePower n).realize := by
  refine AlgebraicComplexity.Tensor.Restricts.partitionedBlockMap
    (P.positivePower n) (Q.positivePower n)
    (fun c ↦ positiveWordMap (dict c) n)
    (AlgebraicComplexity.Tensor.positiveWordBlockMap (K := K) (V := V) (W := W) dict φ n)
    (AlgebraicComplexity.Tensor.positiveWordMap_injOn_support P dict hinj n)
    (AlgebraicComplexity.Tensor.positivePower_support_image P Q dict hsupport hinj n)
    (fun s hs t ht ↦ ?_)
  subst ht
  rw [AlgebraicComplexity.Tensor.map_partitionedBlockMap_block]
  exact congrArg
    (map (blockInclude (K := K) (V := PositivePowerBlockSpace K W n)
      (fun c ↦ positiveWordMap (dict c) n (s c))))
    (AlgebraicComplexity.Tensor.map_positiveWordBlockMap_constituent P Q dict φ
      (fun u hu ↦ AlgebraicComplexity.Tensor.map_partitionedBlockMap_constituent P Q dict φ u
        (hconstituent u hu _ rfl)) n s hs)

end BlockMapPower

end AlgebraicComplexity.Tensor
