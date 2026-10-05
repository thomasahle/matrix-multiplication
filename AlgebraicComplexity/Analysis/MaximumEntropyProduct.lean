import AlgebraicComplexity.Analysis.MaximumEntropyMappedFiber
import AlgebraicComplexity.Probability.Coupling
import AlgebraicComplexity.Probability.ReindexBasic

/-!
# Tensorization and reindexing of maximum-entropy mapped fibers

The method of types often replaces one structured letter by a tuple of independent letters.  If
each one-letter law maximizes entropy subject to its visible coordinates, their independent
product maximizes entropy subject to the paired coordinates.  This module proves that fact for an
arbitrary finite family of dependent coordinate alphabets.  It also proves invariance under
equivalences of both the source alphabet and each visible coordinate alphabet.

These are generic probability statements.  In particular, a client with a 64-letter tensor
support should prove it equivalent to a triple product of four-letter supports and invoke the
theorems here; it should not enumerate 64 entropy cases.
-/

open scoped BigOperators

namespace AlgebraicComplexity.WordType

universe u v w x y

variable {I : Type u} {J : Type v} {C : Type w}
variable {A : C → Type x} {B : C → Type y}
variable [Fintype I] [Fintype J] [Fintype C]
variable [DecidableEq I] [DecidableEq J]
variable [∀ c, Fintype (A c)] [∀ c, Fintype (B c)]
variable [∀ c, DecidableEq (A c)] [∀ c, DecidableEq (B c)]

/-- Pair two dependent coordinate systems letterwise on the Cartesian product alphabet. -/
def productCoordinate
    (left : ∀ c, I → A c) (right : ∀ c, J → B c) :
    ∀ c, I × J → A c × B c :=
  fun c ij ↦ (left c ij.1, right c ij.2)

omit [Fintype C] in
/-- Independent products of maximum-entropy representatives maximize entropy in the paired
mapped-coordinate fiber.

Proof sketch: an arbitrary competing law on `I × J` is a coupling of its two coordinate
marginals.  Equality of every paired visible pushforward implies that each coordinate marginal
lies in the corresponding one-letter mapped fiber.  Entropy subadditivity bounds the competitor
by the sum of those two marginal entropies; one-letter maximality and entropy additivity of the
independent product finish the proof. -/
theorem IsMaximumEntropyInMappedFiber.product
    (left : ∀ c, I → A c) (right : ∀ c, J → B c)
    (p : ProbabilityVector I) (q : ProbabilityVector J)
    (hp : IsMaximumEntropyInMappedFiber left p)
    (hq : IsMaximumEntropyInMappedFiber right q) :
    IsMaximumEntropyInMappedFiber (productCoordinate left right) (p.product q) := by
  intro joint hjoint
  let jointLeft := joint.pushforward Prod.fst
  let jointRight := joint.pushforward Prod.snd
  have hcoupling := ProbabilityVector.IsCoupling.marginals joint
  have hreference := ProbabilityVector.product_isCoupling p q
  have hleft : ∀ c, jointLeft.pushforward (left c) = p.pushforward (left c) := by
    intro c
    have hjointPair := hcoupling.pushforward_prodMap (left c) (right c)
    have hrefPair := hreference.pushforward_prodMap (left c) (right c)
    calc
      jointLeft.pushforward (left c) =
          (joint.pushforward (productCoordinate left right c)).pushforward Prod.fst :=
        hjointPair.1.symm
      _ = ((p.product q).pushforward
          (productCoordinate left right c)).pushforward Prod.fst := by
        rw [hjoint c]
      _ = p.pushforward (left c) := hrefPair.1
  have hright : ∀ c, jointRight.pushforward (right c) = q.pushforward (right c) := by
    intro c
    have hjointPair := hcoupling.pushforward_prodMap (left c) (right c)
    have hrefPair := hreference.pushforward_prodMap (left c) (right c)
    calc
      jointRight.pushforward (right c) =
          (joint.pushforward (productCoordinate left right c)).pushforward Prod.snd :=
        hjointPair.2.symm
      _ = ((p.product q).pushforward
          (productCoordinate left right c)).pushforward Prod.snd := by
        rw [hjoint c]
      _ = q.pushforward (right c) := hrefPair.2
  calc
    joint.entropy ≤ jointLeft.entropy + jointRight.entropy := hcoupling.entropy_le_add
    _ ≤ p.entropy + q.entropy := add_le_add (hp jointLeft hleft) (hq jointRight hright)
    _ = (p.product q).entropy := (ProbabilityVector.entropy_product p q).symm

variable {T : Type v} [Fintype T]

variable {D : Type v} [Fintype D]

/-- Reorder a finite family of dependent visible coordinates. -/
def permuteCoordinate (coordinate : ∀ c, I → A c) (e : C ≃ D) :
    ∀ d, I → A (e.symm d) :=
  fun d ↦ coordinate (e.symm d)

/-- Transport a dependent coordinate system to an equivalent source alphabet. -/
def reindexCoordinate (coordinate : ∀ c, I → A c) (e : I ≃ T) :
    ∀ c, T → A c :=
  fun c ↦ coordinate c ∘ e.symm

/-- Relabel every visible coordinate alphabet by an equivalence. -/
def equivCoordinate (coordinate : ∀ c, I → A c) (e : ∀ c, A c ≃ B c) :
    ∀ c, I → B c :=
  fun c ↦ e c ∘ coordinate c

omit [Fintype C] [DecidableEq I] in
/-- Replacing every visible statistic by an equivalent labelling preserves maximum entropy in its
mapped fiber.

Proof sketch: push equality of the relabelled laws through each inverse equivalence.  Composition
then cancels the equivalence, so the competitor has the original visible laws.  The reference
maximum-entropy theorem applies without changing either source probability law. -/
theorem IsMaximumEntropyInMappedFiber.equivCoordinate
    (coordinate : ∀ c, I → A c) (e : ∀ c, A c ≃ B c)
    (p : ProbabilityVector I)
    (hp : IsMaximumEntropyInMappedFiber coordinate p) :
    IsMaximumEntropyInMappedFiber (equivCoordinate coordinate e) p := by
  intro competitor hcompetitor
  apply hp competitor
  intro c
  have hcancel (law : ProbabilityVector I) :
      (law.pushforward (WordType.equivCoordinate coordinate e c)).pushforward (e c).symm =
        law.pushforward (coordinate c) := by
    rw [ProbabilityVector.pushforward_comp]
    congr 1
    funext i
    simp [WordType.equivCoordinate]
  rw [← hcancel competitor, ← hcancel p, hcompetitor c]

omit [Fintype C] [DecidableEq I] in
/-- Maximum entropy in a mapped-coordinate fiber is invariant under equivalence of source
alphabets.

Proof sketch: pull a competitor back along the inverse equivalence.  Pushforward commutes with
this relabelling, so the pulled law has the original mapped coordinates.  Apply the original
maximum-entropy theorem and then erase both relabellings using entropy invariance. -/
theorem IsMaximumEntropyInMappedFiber.reindex
    (coordinate : ∀ c, I → A c) (e : I ≃ T)
    (p : ProbabilityVector I)
    (hp : IsMaximumEntropyInMappedFiber coordinate p) :
    IsMaximumEntropyInMappedFiber (reindexCoordinate coordinate e) (p.reindex e) := by
  intro competitor hcompetitor
  have hfiber : ∀ c,
      (competitor.reindex e.symm).pushforward (coordinate c) =
        p.pushforward (coordinate c) := by
    intro c
    calc
      (competitor.reindex e.symm).pushforward (coordinate c) =
          competitor.pushforward (coordinate c ∘ e.symm) :=
        ProbabilityVector.pushforward_reindex (coordinate c) e.symm competitor
      _ = (p.reindex e).pushforward (coordinate c ∘ e.symm) := hcompetitor c
      _ = p.pushforward (coordinate c) := by
        rw [ProbabilityVector.pushforward_reindex]
        congr 1
        funext i
        simp
  have h := hp (competitor.reindex e.symm) hfiber
  simpa using h

end AlgebraicComplexity.WordType
