/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.DirectSumPowerCoherence
import AlgebraicComplexity.Tensor.IndexedDegeneration
import AlgebraicComplexity.Tensor.PowerZeroUnit

/-!
# The binomial expansion of a power of a binary direct sum

Layer 1 (`AlgebraicComplexity/Tensor/`).  A tensor power of a binary direct sum splits into
`2 ^ n` blocks, the block indexed by a word `w : Fin n → Bool` being the ordered product of the
letters chosen by `w`.  Grouping the blocks by the number of `A`-letters turns the splitting into
CW90's *binomial expansion*

`(A ⊞ B)^{⊗n} ≅ ⊕_{j ≤ n} (binom(n,j) copies of A^{⊗j} ⊠ B^{⊗(n-j)})`.

This module proves the expansion in the form in which it is used: a single **Pascal step**,
carrying a mixed prefix `A^{⊗k} ⊠ B^{⊗m}` that records the letters already read.  Iterating the
step reproduces the binomial coefficients without ever naming them, exactly as the algebraic
identity `α^k β^m (α+β)^{n+1} = α^{k+1} β^m (α+β)^n + α^k β^{m+1} (α+β)^n` does in
`Tensor/AsymptoticRankCalculus.lean`.

The difference from that file is the direction of the information.
`rank_external_power_directSum_le` there needs only *subadditivity of rank* along the splitting,
so it never produces the splitting itself: it applies `rank_directSum_le` at every step and
carries a real inequality.  A **value** lower bound instead needs the splitting as a relation
between tensors, because each block is afterwards degenerated separately.  The isomorphisms that
make the induction work are shared verbatim with that proof: `Isomorphic.external_directSum`,
`Isomorphic.external_power_succ`, and the two prefix-absorption steps
`Isomorphic.externalPrefix_absorb_left` and `Isomorphic.externalPrefix_absorb_right`, all of which
live in the tensor-only `Tensor/DirectSumPowerCoherence.lean` shared by this construction and the
asymptotic-rank proof.

## Principal results

* `Isomorphic.directSum` — legwise isomorphisms are compatible with binary direct sums.  This is
  the isomorphism companion of `Restricts.directSum`.
* `Isomorphic.externalPrefix_power_directSum_succ` — **the expansion**, one Pascal step.
* `Isomorphic.externalPrefix_power_directSum_zero` — the exhausted remaining power.
* `Restricts.power_directSum_externalPrefix` — a power of `A ⊞ B` restricts onto a mixed prefix
  followed by a shorter power of `A ⊞ B`, which is how a client enters the induction with a
  nonempty prefix.
* `directSumPair`, `Restricts.directSum_indexedPair`, `Restricts.indexedPair_directSum` — the
  identification of a binary direct sum with an indexed direct sum over `Fin 2`, in the ambient
  pair space.
* `PolynomialDegenerates.directSum` — **two polynomial degenerations assemble into one
  degeneration of the binary direct sums.**  `Tensor/IndexedDegeneration.lean` proves the indexed
  form, including the synchronization of the two leading degrees; the identification above is what
  makes it applicable to the binary operation, and it is what a value calculus needs in order to
  degenerate the blocks of the expansion independently.

## References

* D. Coppersmith and S. Winograd, *Matrix multiplication via arithmetic progressions*,
  J. Symbolic Computation 9 (1990), 251--280, §8 (`[CoppersmithWinograd1990]`).
-/

namespace AlgebraicComplexity.Tensor

universe u v w z

variable {K : Type u} [CommSemiring K]
variable {U : Leg → Type z} [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- **Legwise isomorphisms are compatible with binary direct sums.**  This is the isomorphism
companion of `Tensor.Restricts.directSum`.

Proof sketch: take the legwise product of the two equivalences; `Tensor.map_directSum` computes
its action on a direct sum. -/
theorem Isomorphic.directSum {V' : Leg → Type*} {W' : Leg → Type*}
    [∀ c, AddCommMonoid (V' c)] [∀ c, Module K (V' c)]
    [∀ c, AddCommMonoid (W' c)] [∀ c, Module K (W' c)]
    {T : Tensor3 K V} {T' : Tensor3 K V'} {S : Tensor3 K W} {S' : Tensor3 K W'}
    (hT : Isomorphic T T') (hS : Isomorphic S S') :
    Isomorphic (Tensor.directSum T S) (Tensor.directSum T' S') := by
  rcases hT with ⟨f, hf⟩
  rcases hS with ⟨g, hg⟩
  have hT' : Tensor.map (fun c ↦ (f c).toLinearMap) T = T' := by
    simpa [PiTensorProduct.congr] using hf
  have hS' : Tensor.map (fun c ↦ (g c).toLinearMap) S = S' := by
    simpa [PiTensorProduct.congr] using hg
  refine ⟨fun c ↦ (f c).prodCongr (g c), ?_⟩
  have hmap :=
    Tensor.map_directSum (fun c ↦ (f c).toLinearMap) (fun c ↦ (g c).toLinearMap) T S
  rw [hT', hS'] at hmap
  simpa [PiTensorProduct.congr] using hmap

/-- **The binomial expansion of a power of a direct sum, one Pascal step.**

`A^{⊗k} ⊠ B^{⊗m} ⊠ (A ⊞ B)^{⊗(n+1)}` is the direct sum of the two longer-prefix mixed powers
obtained by reading one more letter.  Iterating the step from the empty prefix produces, after `n`
steps, one summand for every word in `{A,B}^n`, hence `binom(n,j)` copies of
`A^{⊗j} ⊠ B^{⊗(n-j)}`; the count never has to be named, because it is generated by the shape of
the recursion.

Proof sketch: `Isomorphic.external_power_succ` exposes the last factor `A ⊞ B`,
`Isomorphic.external_directSum` distributes the product over it, and the two halves are absorbed
into the prefix by `externalPrefix_absorb_left` and `externalPrefix_absorb_right`. -/
theorem Isomorphic.externalPrefix_power_directSum_succ (A : Tensor3 K V) (B : Tensor3 K W)
    (k m n : ℕ) :
    Isomorphic
      (Tensor.external (Tensor.external (Tensor.power A k) (Tensor.power B m))
        (Tensor.power (Tensor.directSum A B) (n + 1)))
      (Tensor.directSum
        (Tensor.external (Tensor.external (Tensor.power A (k + 1)) (Tensor.power B m))
          (Tensor.power (Tensor.directSum A B) n))
        (Tensor.external (Tensor.external (Tensor.power A k) (Tensor.power B (m + 1)))
          (Tensor.power (Tensor.directSum A B) n))) :=
  (Isomorphic.external_power_succ (Tensor.external (Tensor.power A k) (Tensor.power B m))
      (Tensor.directSum A B) n).trans
    ((Isomorphic.external_directSum
        (Tensor.external (Tensor.external (Tensor.power A k) (Tensor.power B m))
          (Tensor.power (Tensor.directSum A B) n)) A B).trans
      ((Isomorphic.externalPrefix_absorb_left A B (Tensor.directSum A B) k m n).directSum
        (Isomorphic.externalPrefix_absorb_right A B (Tensor.directSum A B) k m n)))

/-- The base of the expansion: an exhausted power leaves the mixed prefix alone. -/
theorem Isomorphic.externalPrefix_power_directSum_zero (A : Tensor3 K V) (B : Tensor3 K W)
    (k m : ℕ) :
    Isomorphic
      (Tensor.external (Tensor.external (Tensor.power A k) (Tensor.power B m))
        (Tensor.power (Tensor.directSum A B) 0))
      (Tensor.external (Tensor.power A k) (Tensor.power B m)) :=
  Isomorphic.powerZeroExternalRight
    (Tensor.external (Tensor.power A k) (Tensor.power B m)) (Tensor.directSum A B)

/-- **Entering the expansion with a nonempty prefix.**  A power of `A ⊞ B` of length `k + m + n`
restricts onto `A^{⊗k} ⊠ B^{⊗m} ⊠ (A ⊞ B)^{⊗n}`: the first `k` factors are projected onto their
left summand, the next `m` onto their right summand, and the remaining `n` are kept.

This is what lets a value client avoid the zeroth powers `A^{⊗0}` and `B^{⊗0}`, whose value is not
implied by the value of `A` or of `B`. -/
theorem Restricts.power_directSum_externalPrefix (A : Tensor3 K V) (B : Tensor3 K W)
    (k m n : ℕ) :
    Restricts (Tensor.power (Tensor.directSum A B) (k + m + n))
      (Tensor.external (Tensor.external (Tensor.power A k) (Tensor.power B m))
        (Tensor.power (Tensor.directSum A B) n)) := by
  refine (isomorphic_external_power (Tensor.directSum A B) (k + m) n).symm.restricts.trans ?_
  refine Restricts.external ?_ (Restricts.refl _)
  refine (isomorphic_external_power (Tensor.directSum A B) k m).symm.restricts.trans ?_
  exact Restricts.external ((Restricts.directSum_left A B).power k)
    ((Restricts.directSum_right A B).power m)

/-! ## Binary direct sums as indexed direct sums over `Fin 2`

`Tensor/IndexedDegeneration.lean` assembles finitely many polynomial degenerations into one
degeneration of the indexed direct sums, synchronizing their leading degrees.  Binary direct sums
are built from `Prod` rather than `DFinsupp`, so that theorem does not apply to them directly.
The bridge below removes the difference: both summands of `T ⊞ S` are placed inside the *common*
ambient pair space, where the family of the two of them is a constant-space family over `Fin 2`
and the indexed theory applies verbatim. -/

section BinaryPair

variable {V' : Leg → Type*} [∀ c, AddCommMonoid (V' c)] [∀ c, Module K (V' c)]
variable {W' : Leg → Type*} [∀ c, AddCommMonoid (W' c)] [∀ c, Module K (W' c)]

/-- **The two summands of `T ⊞ S`, both viewed inside the ambient pair space.**  Their indexed
direct sum over `Fin 2` is the binary direct sum, and their ordinary sum is its ambient
representative. -/
noncomputable def directSumPair (T : Tensor3 K V) (S : Tensor3 K W) :
    Fin 2 → Tensor3 K (fun c ↦ V c × W c) :=
  fun i ↦ if i = 0 then map includeLeft T else map includeRight S

@[simp] theorem directSumPair_zero (T : Tensor3 K V) (S : Tensor3 K W) :
    directSumPair T S 0 = map includeLeft T := if_pos rfl

@[simp] theorem directSumPair_one (T : Tensor3 K V) (S : Tensor3 K W) :
    directSumPair T S 1 = map includeRight S := if_neg (by decide)

theorem sum_directSumPair (T : Tensor3 K V) (S : Tensor3 K W) :
    ∑ i, directSumPair T S i = directSum T S := by
  rw [Fin.sum_univ_two, directSumPair_zero, directSumPair_one, directSum]

/-- The legwise map placing the ambient pair space into the `Fin 2`-indexed direct sum of two
copies of itself, the first coordinate into block `0` and the second into block `1`. -/
private noncomputable def pairBlockMap (V : Leg → Type v) (W : Leg → Type w)
    [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
    [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)] :
    ∀ c, (V c × W c) →ₗ[K]
      IndexedDirectSumSpace K (fun _ : Fin 2 ↦ fun c ↦ V c × W c) c :=
  fun c ↦ LinearMap.coprod
    (indexedInclude (K := K) (V := fun _ : Fin 2 ↦ fun c ↦ V c × W c) 0 c ∘ₗ
      LinearMap.inl K (V c) (W c))
    (indexedInclude (K := K) (V := fun _ : Fin 2 ↦ fun c ↦ V c × W c) 1 c ∘ₗ
      LinearMap.inr K (V c) (W c))

/-- **A binary direct sum restricts onto the indexed direct sum of its two ambient summands.**
The two summands occupy disjoint blocks of the pair space, so separating them is an exact
legwise restriction. -/
theorem Restricts.directSum_indexedPair (T : Tensor3 K V) (S : Tensor3 K W) :
    Restricts (Tensor.directSum T S) (Tensor.indexedDirectSum (directSumPair T S)) := by
  classical
  refine ⟨pairBlockMap (K := K) V W, ?_⟩
  have hleft : (fun c ↦ pairBlockMap (K := K) V W c ∘ₗ
      Tensor.includeLeft (K := K) (V := V) (W := W) c) =
      fun c ↦ Tensor.indexedInclude (K := K) (V := fun _ : Fin 2 ↦ fun c ↦ V c × W c) 0 c ∘ₗ
        Tensor.includeLeft (K := K) (V := V) (W := W) c := by
    funext c
    exact LinearMap.coprod_inl _ _
  have hright : (fun c ↦ pairBlockMap (K := K) V W c ∘ₗ
      Tensor.includeRight (K := K) (V := V) (W := W) c) =
      fun c ↦ Tensor.indexedInclude (K := K) (V := fun _ : Fin 2 ↦ fun c ↦ V c × W c) 1 c ∘ₗ
        Tensor.includeRight (K := K) (V := V) (W := W) c := by
    funext c
    exact LinearMap.coprod_inr _ _
  have hrhs : Tensor.indexedDirectSum (directSumPair T S) =
      Tensor.map (Tensor.indexedInclude (K := K) (V := fun _ : Fin 2 ↦ fun c ↦ V c × W c) 0)
          (Tensor.map Tensor.includeLeft T) +
        Tensor.map (Tensor.indexedInclude (K := K) (V := fun _ : Fin 2 ↦ fun c ↦ V c × W c) 1)
          (Tensor.map Tensor.includeRight S) := by
    unfold Tensor.indexedDirectSum
    rw [Fin.sum_univ_two, directSumPair_zero, directSumPair_one]
  rw [hrhs, Tensor.directSum, LinearMap.map_add, map_map_comp, map_map_comp, hleft, hright,
    ← map_map_comp, ← map_map_comp]

/-- **The indexed direct sum of the two ambient summands restricts back onto the binary direct
sum.**  Both blocks are folded back into the pair space they came from. -/
theorem Restricts.indexedPair_directSum (T : Tensor3 K V) (S : Tensor3 K W) :
    Restricts (Tensor.indexedDirectSum (directSumPair T S)) (Tensor.directSum T S) := by
  have h := Restricts.indexedDirectSum_to_sum
    (T := directSumPair T S) (S := directSumPair T S) (fun i ↦ Restricts.refl _)
  rwa [sum_directSumPair] at h

/-- A tensor pushed into the left summand of a pair space restricts back onto itself. -/
theorem Restricts.map_includeLeft (T : Tensor3 K V) :
    Restricts (Tensor.map (Tensor.includeLeft (K := K) (V := V) (W := W)) T) T := by
  refine ⟨fun c ↦ LinearMap.fst K (V c) (W c), ?_⟩
  rw [map_map_comp]
  have : (fun c ↦ (LinearMap.fst K (V c) (W c)) ∘ₗ
      Tensor.includeLeft (K := K) (V := V) (W := W) c) =
      fun c ↦ LinearMap.id (R := K) (M := V c) := by
    funext c
    exact LinearMap.ext fun x ↦ rfl
  rw [this, map_id]
  rfl

/-- A tensor pushed into the right summand of a pair space restricts back onto itself. -/
theorem Restricts.map_includeRight (S : Tensor3 K W) :
    Restricts (Tensor.map (Tensor.includeRight (K := K) (V := V) (W := W)) S) S := by
  refine ⟨fun c ↦ LinearMap.snd K (V c) (W c), ?_⟩
  rw [map_map_comp]
  have : (fun c ↦ (LinearMap.snd K (V c) (W c)) ∘ₗ
      Tensor.includeRight (K := K) (V := V) (W := W) c) =
      fun c ↦ LinearMap.id (R := K) (M := W c) := by
    funext c
    exact LinearMap.ext fun x ↦ rfl
  rw [this, map_id]
  rfl

/-- **Two polynomial degenerations assemble into one degeneration of the binary direct sums.**

This is the binary companion of `PolynomialDegenerates.indexedDirectSum`, and the missing rule
for degenerating the blocks of a direct-sum expansion independently.  In particular the two
component degenerations need not have a common leading degree: the indexed theorem synchronizes
them.

Proof sketch: separate the summands into the two blocks of the pair space
(`Restricts.directSum_indexedPair`), degenerate the blocks independently, and fold the blocks back
(`Restricts.indexedPair_directSum`).  On each block the component degeneration is the given one,
conjugated by the inclusion and the projection of the pair space. -/
theorem PolynomialDegenerates.directSum {T : Tensor3 K V} {T' : Tensor3 K V'}
    {S : Tensor3 K W} {S' : Tensor3 K W'}
    (hT : PolynomialDegenerates T T') (hS : PolynomialDegenerates S S') :
    PolynomialDegenerates (Tensor.directSum T S) (Tensor.directSum T' S') := by
  classical
  refine (PolynomialDegenerates.of_restricts (Restricts.directSum_indexedPair T S)).trans ?_
  refine (PolynomialDegenerates.indexedDirectSum
    (S := directSumPair T' S') ?_).trans
    (PolynomialDegenerates.of_restricts (Restricts.indexedPair_directSum T' S'))
  intro i
  fin_cases i
  · exact ((PolynomialDegenerates.of_restricts (Restricts.map_includeLeft (W := W) T)).trans
      hT).trans (PolynomialDegenerates.of_restricts ⟨Tensor.includeLeft, rfl⟩)
  · exact ((PolynomialDegenerates.of_restricts (Restricts.map_includeRight (V := V) S)).trans
      hS).trans (PolynomialDegenerates.of_restricts ⟨Tensor.includeRight, rfl⟩)

end BinaryPair

end AlgebraicComplexity.Tensor
