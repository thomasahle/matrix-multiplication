# Lower-bound and barrier roadmap

Machine-checked inventory (2026-08-25) of every lower-bound-flavored statement in the three
lower-bound papers under `papers/`, cross-referenced against the Lean tree. Sources were read
in full: Hopcroft–Kerr 1971 (SIAM J. Appl. Math. 20(1); local copy is missing journal p. 36,
so its references [3],[5],[6] cannot be resolved locally), Alman–Vassilevska Williams
arXiv:1810.08671 ("limits on all known approaches"), and Alman–Williams STOC 2017
(probabilistic rank / rigidity). Update this file as rows land.

## Proved in the tree

| Statement | Source | Lean home |
| --- | --- | --- |
| `rank ⟨2,2,2⟩ = 7` over **every field** (lower bound via the substitution method; upper via Strassen) | Winograd 1971 (cited by HK); HK 1971 Thm 3 proves the `≥ 7` lower bound over the mod-2 coefficient domain — the Lean theorem is the stronger arbitrary-field statement, following Bläser–Christandl–Zuiddam CJTCS 2018 | `Examples/WinogradLowerBound.lean` (`rank_matrixMultiplication_two`, `Winograd.Computes.length_ge_seven`) |
| `⟨m,n,p⟩` substitution bounds `np+1`, `np+2`; `⟨2,2,2⟩ ≥ 5, ≥ 6` stepping stones | substitution method (HK/Winograd lineage) | `Tensor/SubstitutionMethod.lean`, `Examples/SmallMatrixLowerBounds.lean` |
| Border-rank conciseness: concise legs bound border rank; MM border-rank lower bounds | notes Thm 3.4 lineage | `Tensor/BorderConcise.lean`, `MatrixMultiplication/BorderConcise.lean` |
| Slice-rank calculus; Tao's diagonal lemma `sliceRank(diag n) = n`; size-`m` diagonal restriction of `T` forces `m ≤ sliceRank T` (finite barrier core) | Tao 2016; engine of AVW barriers | `Tensor/SliceRank.lean` |

## Hopcroft–Kerr 1971 — remaining targets

| Statement | HK numbering | Tractability |
| --- | --- | --- |
| `⌈(3pn + max(n,p))/2⌉` upper bound for `(p×2)·(2×n)` — `⟨2,2,3⟩ ≤ 11` first | Thm 1 | **`⟨2,2,3⟩ ≤ 11` PROVED** (`Examples/HopcroftKerrUpper.lean`; certificate realizes HK's count — their own term list is in the unobtainable Cornell TR); general `(p,n)` remains |
| `⌈7n/2⌉` lower bound for `(2×2)·(2×n)`, mod-2 coefficients | Thm 2 (via Lemmas 3–5, nine-group averaging) | hard — the substitution API covers pieces; the averaging is new machinery |
| `rank ⟨2,3,3⟩ = 15` | unnumbered ("similar techniques"; proof only in TR) | hard |
| commutativity saves at most a factor 2 | §3 remark | tractable once the commutative (non-bilinear) model exists — blocked on `RankComplexity` growth |

## AVW 1810.08671 — barrier program (ranked near-term first)

| Statement | AVW numbering | Tractability |
| --- | --- | --- |
| `T_G` monomially degenerates to a generalized CW tensor of parameter `|G|−2` | Thm 7.2 | **PROVED** — `Examples/GeneralizedCoppersmithWinograd.lean` (full monomial certificate over any finite group, any `CommSemiring`; generalized-CW Def 3.1 formalized with the classical CW bridge; border rank of `CW_q^σ` for general `σ` deliberately not claimed, matching AVW's own conditional) |
| `CW_q` is not a sub-tensor of `T_G` for abelian `|G| < 2q` | Lemma 6.3 (+6.2) | **PROVED** — `Examples/CoppersmithWinogradGroupExclusion.lean` (faithful `IsSubTensorVia` notion, fidelity-documented; stated with weaker hypotheses than the paper) |
| zeroing-out of `T_G` to an independent diagonal ⇒ tri-colored sum-free set of that size | Lemma 6.1, Cor 6.1 | tractable — elementary once `T_G` and sum-free sets are defined |
| `CW_q ⊄ T_G` for `|G| = q+2`, `q = 3..9` (nonabelian cases) | Thm 6.2 | tractable but tedious (kernel-`decide` budget) |
| `Ī(T) ≥ R̃(T)^{6/ω_g(T) − 2}` — the engine turning independence-number upper bounds into ω barriers | Thm 4.1 / Cor 4.3 | hard — requires the Galactic-method model (`ω_g`) and asymptotic independence number `Ī` |
| near-uniform mass distribution / corner-term barriers | Thm 5.1–5.3, Cor 5.1 | hard (Hoeffding + fiber counting; the repo probability layer helps, `Ī` framework prerequisite) |
| headline: a universal `c > 2` with `ω_g ≥ c` for **every** generalized CW tensor | Thm 7.1 = Lemmas 7.1/7.2 | **PROVED IN FULL** (`Examples/GeneralizedCoppersmithWinogradBarrier.lean`, `avw_theorem_seven_one`): universal constant `min(60000/29999, 6/(3 − cornerExponent 7)) ≥ 2 + 1/15000` for every generalized CW tensor and every `σ`, for the coordinate galactic exponent; Lemma 7.1 via Corollary 5.1 (every `q`), Lemma 7.2 via Theorem 5.1 (`q ≥ 6`) and Theorem 5.3 (`q ≥ 24`); side condition discharged |
| `ω_g(T_G) > 2` for every finite group | Thm 6.1 | **PROVED conditionally** (`Examples/GroupTensorBarrier.lean`): `SawinBound G → 2 < coordinateGalacticExponent (T_G)`, with Sawin's theorem a named `Prop` obligation per DESIGN; Lemma 6.1 proved unconditionally as an equality |
| `Ī` lower bounds / sum-free constructions | Thm 7.3, 7.4 | research-scale (consumes CW90's laser analysis as a lower bound on `ω_g`) |
| lower-triangular tensor barriers | Thm 7.5, 7.6 | hard (needs Thm 5.x machinery) |

The formalization order the inventory recommends: Thm 7.2 and Lemma 6.3 first (self-contained,
API-exercising), then the `Ī`/`ω_g` framework (Thm 4.1) as the gateway to everything in
sections 5 and 7. The slice-rank module is the intended finite substrate: asymptotic slice
rank and monomial-degeneration semicontinuity (documented as future work in
`Tensor/SliceRank.lean`) are the two missing bridges from it to `Ī`.

## Alman–Williams STOC 2017 — honest classification

Nothing in this paper bounds ω or MM tensor rank. Its content is: rigidity **upper** bounds
(Walsh–Hadamard is not rigid — a negative result killing one route to circuit lower bounds),
conditional implications (rigidity ⇒ circuit lower bounds; sign-rank rigidity ⇒ LTF∘LTF
bounds), and probabilistic-rank/communication equivalences. These live in a Boolean-circuit
layer this repository deliberately does not have; the paper contributes **no formalization
targets** to the ω roadmap. Recorded here so the goal's scope over `papers/` is complete.

## Decisions (2026-08-25)

Approved for formalization: the certificate quick wins (Laderman, AlphaTensor/AlphaEvolve,
HK Thm 1 upper bounds, 21-term border ⟨3,3,3⟩), Koszul flattenings, Bläser 5/2·n²−3n (with the
border-substitution ~3n² rank bound as the follow-on landmark), asymptotic
subrank/independence-number framework toward the FULL AVW headline barriers, Schönhage's
partial-matrix-product τ-theorem, a first real rectangular theorem (interpolation bound
ω(κ) ≤ κ·ω + 2(1−κ) and convexity; Coppersmith α as the stretch landmark), and Proposition
2.7's recursive compilation. Declined: Cohn–Umans group-theoretic method (no record-setting
application; revisit only if the barrier work needs more than T_G). Deferred: Strassen support
functionals / CVZ irreversibility (AVW's own route via asymptotic slice rank is the direct
path; CVZ is an optional later reformulation), de Groote uniqueness (valuable but does not
simplify the approved proofs).

## Tranche results (2026-08-25, second wave)

Landed (see git history for the full list): Laderman `⟨3,3,3⟩ ≤ 23` with omega corollary;
`⟨2,2,3⟩ ≤ 11`; char-2 flip-graph decompositions `⟨3,2,3⟩ ≤ 15`, `⟨3,3,3⟩ ≤ 23` discovered
and kernel-verified in-session (AlphaTensor/AlphaEvolve factor tables are NOT in local
sources — nothing was transcribed from memory; the general bitmask harness is ready if the
Nature/AlphaEvolve data arrives); Koszul flattening method + independent `rank ⟨2,2,2⟩ ≥ 6`
(border version blocked on `K[ε]` exterior-power base change — documented); substitution
kill-chains + general `rank ⟨n,n,n⟩ ≥ 2n² − n` (the uniform fragment's provable optimum;
Bläser's 5/2·n² needs the sandwich normal form at scale — named obstruction; `2n² − 1` is
Alder–Strassen, a different method); Schönhage partial τ-theorem (Thm 4.1, infinite fields)
with the Bini corollary `ω < 2.695` now **unconditional** over any infinite field
(`Examples/Bini.lean`, `bini_omega_lt`); Prop 2.7 forward direction complete; rectangular convexity +
interpolation + `α = 1 ↔ ω = 2`; finite independence number `I(T)` with the slice-rank
bridge, plus `BARRIER_FRAMEWORK.md` (14 dependency-ordered milestones to AVW Thm 7.1, two
documented AVW errata, Sawin's theorem flagged as the one external named obligation).

## Priority decisions (2026-08-25, second round)

- **Next priority: the AVW headline barriers** — asymptotic `Ī` via the Fekete engine,
  Theorem 4.1's engine, and the CW entropy optimization, per BARRIER_FRAMEWORK.md's milestone
  order; Sawin's theorem enters as a named `Prop` obligation (no Lean source exists).
- **Descoped**: HK's general `⌈7n/2⌉` mod-2 lower
  bound, `⟨2,3,3⟩ = 15`, and the full Bläser `5/2·n²` (its sandwich-normal-form obstruction
  stands recorded; `2n² − n` is the library's general bound).
- **AlphaTensor/AlphaEvolve factor tables**: to be fetched online (Nature supplement /
  AlphaEvolve release) — explicitly not a priority; the bitmask harness waits.

## Ideas for improving the lower bounds (2026-08-26)

Collected while closing the AVW program; none is started. "Lower bound" here means both the barrier
constants (`ω_g ≥ …`) and the independence-number / sum-free lower bounds (`Ī ≥ …`).

### Barrier constants (Theorem 7.1 and relatives)
1. **The binding term is now Lemma 7.2's route-2 constant `60000/29999`**, not the corner term. Its slack
   comes from three crude steps in `avw_lemma_seven_two_of_six_le`: the part-measure bound `(q+1)²`
   (AVW's misprint corrected, but still counted with the whole leg), the polynomial-loss buffers in the
   method-of-types split, and using only one of the two corner families. Re-running route 2 with the sharp
   `2ε²` tail exponent and both corners should move `2 + 1/15000` visibly; a per-`q` table
   (`q = 5..12`) would show where the minimum sits.
2. **Ī upper bounds for `CW_q` are far from the truth.** The sandwich `6 + 6/25 ≤ Ī(CW_6) < 8` shows
   `cornerBound` (Corollary 5.1) loses most of the gap. AVW's `Ī ≤ q^{1−cornerExponent}` uses only one
   corner; a two-corner / structural-sparsity argument (`asymptoticIndependenceNumber_twoCornerTable_lt_two`
   is the toy model) applied to the full `CW_q` table would tighten every barrier at once.
3. **Slice-rank route**: `Ī(T) ≤` asymptotic slice rank of the coordinate table is basis-independent and
   AVW's Theorem 3.2 (Sawin) sits there; a repository slice-rank bound on `CW_q` (the diagonal lemma
   already exists, `Tensor/SliceRank.lean`) would give a Sawin-free, unconditional `ω_g(T_G) > 2` for
   the *specific* groups the CW tensors degenerate from, and a second, independent barrier for `CW_q`.
4. **Galactic vs universal**: everything proved is for the coordinate Galactic exponent. The universal
   method barrier (AVW §5, `ω_u`) needs Ī over *all* monomial degenerations; the coordinate-block-word
   machinery (`Tensor/CoordinateBlockWord.lean`) is the natural tool to enumerate them for `CW_q^{⊗2}`
   explicitly and certify the barrier numerically for small `q`.

### Independence-number and sum-free lower bounds (Theorems 7.3, 7.4)
5. **Feed better `ω` analyses into `Ī`**: the cube form is generic — any balanced zeroing out of
   `CW_q^{⊗n}` into `F` copies of `⟨a,a,a⟩` with `F·a^{w} ≥ (q+2)^{(1−δ)n}` gives `Ī ≥ (q+2)^{2/w}`.
   Instantiating the machinery on the six-constituent first-power file gives `Ī(CW_6) ≥ 6.4194…`
   (AVW Remark 7.3); on the `CW^{⊗2}`/`⊗4` analyses (Stothers, Vassilevska Williams, Le Gall,
   `w ≈ 2.373`) it would give `Ī(CW_q) ≥ (q+2)^{2/2.373}` — for `q = 6`, `8^{0.843} = 5.77` in AVW's
   form but, in the cube form with balanced squares, essentially `Ī ≥ (q+2)^{1−o(1)}·`const, closing
   the sandwich from below. The bottleneck is the coordinate shadow of the higher-power extractions
   (M3-style block words on `CW^{⊗2}` blocks).
6. **Tri-colored sum-free sets (7.4)**: `|G|^{(c−ε)n} ≤ f(Gⁿ)` with `c = log((27/4)(|G|−2)²)/(3 log|G|)`;
   the same `ω`-analysis upgrade lifts `c` toward `1 − o(1)`; compare with the Kleinberg–Sawin–Speyer
   `(|G| − ε)^n`-type constructions, which the repository does not have — formalizing KSS's explicit
   construction would also close orders 2 and 3.
7. **Sawin's constant**: `le_sawinConstant` gives `δ ≥ ((27/4)(|G|−2)²)^{1/3}/|G|` for every group;
   with item 5 this tends to `1 − o(1)`, i.e. the Section-6 barrier `ω_g(T_G) ≥ 2 + Ω(1 − δ)` can only be
   as strong as `1 − δ`, which is *small* for large groups — worth stating as a limitation of the
   group-tensor barrier itself.

### Classical rank lower bounds
8. Bläser's `5/2 n² − 3n` (descoped) and Landsberg's border-rank `2n² − log n − 1` (Koszul flattenings
   for general `n`; `KoszulBorderRank.lean` currently proves rank, not border rank — the `K[ε]`
   exterior-power base change is the missing core) are the natural next rungs; the substitution-method
   core in `Tensor/SubstitutionMethod.lean` already handles the Bläser-style steps for `n = 2, 3`.

## The thesis branch (Alman 2019, Ch. 5 = *Limits on the Universal Method*, CCC 2019) — scoped 2026-08-26

The AVW branch (Ī, monomial degenerations, ω_g) is formalized; the thesis branch runs on **asymptotic
slice rank S̃** and the **universal exponent ω_u** (all degenerations) and is new to the tree. Its barrier
constant `2/s` (thesis Thm 5.1, via Prop 4.3 "one MM tensor w.l.o.g.") is strictly stronger than AVW's
`6/(s+2)` (`IndependenceBarrier.lean`), and its block-partition entropy bound (thesis Thm 5.3) gives the
exact value `S̃(CW_6) = 6.44493` — closing the `Ī(CW_6)` sandwich from above and lifting Theorem 7.1's
universal constant from `2 + 1/15000` to ≈ 2.05 (Galactic route) or `2.16805` (universal route, thesis Thm 5.7).
Targets, in order (plan file in the session scratchpad, builders launched the same day):
1. `Tensor/IndependenceBlockEntropy.lean` — thesis Thm 5.3/Prop 5.4 for Ī; instance on `gcwTable`.
2. `Tensor/SliceRankAlong`, `Tensor/AsymptoticSliceRank` (a limsup, not Fekete), `Tensor/SliceRankDegeneration`
   (Prop 5.1 = [TS16, Cor 2]: slice rank is monotone under all degenerations — the branch point).
3. `MatrixMultiplication/UniversalMethod.lean` — ω_u, `ω ≤ ω_u ≤ ω_g`, Prop 4.3, Thm 5.1, Cor 5.2.
4. `Tensor/AsymptoticRank.lean` calculus (direct sums, products, both halves of the power law,
   `R̃⟨a,b,c⟩ ≤ (abc)^{ω/3}`) and Alman–Li Prop 4.4 (duality-free).
5. Later: Alman–Li's constructive degeneration layer (free-lunch speedup, one-slice compression, Thms 6.1/6.3/7.3);
   the numeric headlines need Strassen duality (research-scale core).
Not formalizable from local sources: the AFL `2.3078` bound (no proof in papers/).
9. **Strassen's commutation equations** — DONE for the minimal case 2026-08-27 (`Tensor/StrassenEquations.lean`; `R̲(CW_q^σ) ≥ q+3` for non-involutive σ; open: the general inequality `2(R̲−n) ≥ rank[A_i,A_j]` and the Z-basis-change wrapper for `R̲⟨2,2,2⟩ ≥ 5`) (`Tensor/StrassenEquations.lean`, missing core): M8 found that
   `BorderRankLE (q+2) (genCW K μ σ)` is false for every non-involutive `σ` — the normalized `Z`-slices
   satisfy `[A_{z_i}, A_{z_j}] = ([i=σj] − [j=σi])·E_{q+1,0}`, so `R̲(CW_q^σ) ≥ q+3` (minimal border rank
   fails). Formalizing the equations would (a) turn M8's border-rank hypothesis into a proved dichotomy,
   (b) give the library its first border-rank *lower* bounds beyond conciseness/Koszul, and (c) is CSLib-shaped
   (pure tensor theory).

## Active program 2026-08-28: rectangular matrix multiplication (user directive)

Formalize the rectangular-MM papers: Coppersmith 1982 (`copper-rect1.pdf`, the first `α > 0`),
Coppersmith 1997 (`coppersmith1997.pdf`, `α > 0.29404` via CW machinery), Huang–Pan 1998
(interpolating bounds). The tree has the framework (`MatrixMultiplication/RectangularExponent.lean`:
`rectangularOmega`/`rectangularAlpha`, `RectangularInterpolation.lean`, the partial τ-theorem in
`PartialAsymptoticSum.lean` — likely the exact engine for 1982) but none of the papers' theorems.
Scoping pass running; milestones M-R1… to follow its report.


### Scoping result (2026-08-28) and milestone plan

Sources read in full: Coppersmith 1982 (SIAM J. Comput. 11(3) 467–471), Coppersmith 1997
(J. Complexity 13, 42–49), Huang–Pan 1998 (J. Complexity 14, 257–299).  Exact constants:
1982's `α = 2 log 2/(5 log 5) = 0.1722704…` (general `(k,n)`:
`α = 2 log((k−1)(n−1)+1)/((kn+1) log(kn+1))`, maximal at `k = n = 2`; the direct-sum route of
§4 gives only `2 log 4/(9 log 9) = 0.1402…`), 1997's Theorem 1 value is `α = 0.29462`
(the abstract says `> 0.294`), Huang–Pan's headline is `ω(1,1,2) < 3.333953` at `q = 9, β = 0.016`,
their §3 bound being exactly `7 log 3/log 10 < 3.3399`.

Two facts the scope turned up about the existing tree:

* **Two Huang–Pan theorems are already proved under other names.**  `(8.1)`'s second branch is
  `RectangularInterpolation.lean:545` (`rectangularOmega_le_interpolation_of_eq_two`, whose
  expansion `2 + (ω−2)(κ−κ₀)/(1−κ₀)` is `(2(1−κ) + (κ−κ₀)ω)/(1−κ₀)` identically), and §8.1's
  `g(r) = r − 1 + ω` is `:514`.  Both hold over every commutative semiring.
* **The repo's `ω < 2.41` (`CoppersmithWinogradEasyHashing.lean:937`) *is* Huang–Pan (6.1)/(6.2)
  at `r = 1`**, and `ω < 2.3872` *is* their `f(1) = 2.38719`.  The rectangular bounds are
  `r`-generalizations of pipelines that already work end to end, not new pipelines.

Three missing cores gate everything downstream:

1. **Rectangular compression.**  `Compression.lean:88` only does the square case and
   `AsymptoticSum.lean` deliberately symmetrizes cyclically.  Needed:
   `RankLE (card ι) ⟨q₁,q₂,q₃⟩ → Restricts (⊕_ι ⟨A,B,C⟩) ⟨q₁A, q₂B, q₃C⟩`, four lines over
   `RankCompression.lean:227` and `TypeExtraction.lean:177` (both already rectangular).  At
   `⟨1,F,1⟩` this is the workhorse `⊕_F ⟨A,B,C⟩ ⤳ ⟨A, F·B, C⟩`.
2. **A rectangular exponent packager** — the analogue of `BiniInterpolation.lean:62`, turning a
   family of certificates `RankLE (r s) ⟨A s, C s, A s⟩` with `(A s)^κ ≤ C s` into
   `RectangularMatrixExponentLE K κ τ`.
3. **Leg transposition** `⟨m,n,p⟩ → ⟨n,m,p⟩` for `RankLE`/`BorderRankLE`/`BorderRankLEAt`; only
   the 3-cycle exists (`BorderRank.lean:36`), while Coppersmith 1982 p. 469 reverses two legs.

Milestones, in order:

* **M-R1** — **DONE** (`MatrixMultiplication/RectangularHuangPan.lean`): restate the two already-proved Huang–Pan theorems under their paper names in a
  new `MatrixMultiplication/RectangularHuangPan.lean`, with the §8.1 crossing-point corollary.
* **M-R2** — **DONE**: the three cores above (`Compression.lean`, `Tensor/BorderRankTransport.lean` +
  `MatrixMultiplication/Transpose.lean`, `MatrixMultiplication/RectangularCertificate.lean`).
* **M-R3** — **DONE at `k = q = 2`** (`Examples/SchonhageSecondDesign.lean`): Schönhage's second design as a partial-matrix-multiplication certificate
  (`Examples/SchonhageSecondDesign.lean`, modelled on `Examples/Bini.lean`): pattern
  `I = {(κ,μ) | κ = 0 ∨ μ > 0}`, `J = {(μ,ν) | μ = 0 ∨ ν = 0}`, `BorderRankLEAt (kq+1) 2`.
  Bonus: `PartialAsymptoticSum.lean:1179` then gives Schönhage's `λ(17,26) < 2.6087` at
  `k = q = 4`, beating the tree's current `ω < 2.695`.
* **M-R4** — **DONE** (`borderRankLEAt_matrixMultiplication_of_type`): extract the filling lemma of `PartialAsymptoticSum.lean:1097–1148` at an
  *arbitrary* multiplicity type (the inlined proof currently hard-wires the volume weights
  `x_j = k_j n_j`; Coppersmith's only new step in 1982 is to use the **area** weights `x_j = k_j`).
* **M-R5** (flagship) — **DONE** (`Examples/CoppersmithRectangular1982.lean`): `2 log 2/(5 log 5) ≤ rectangularAlpha F`, i.e. the first `α > 0`, hence
  `17/100 < α`.  Every step lands on an existing lemma; this is what turns
  `RectangularInterpolation.lean` from vacuous (its own non-goals note: "everything in this file is
  vacuously consistent with `α = 0`") into substantive.
* **M-R6a** — **DONE** (`Examples/CoppersmithWinogradEasyRectangularType.lean`): the rectangular type
  layer, with exact `r = 1` regressions. Its assembly (M-R6b) is **DONE** for the sharp
  `r ≤ 1` branch, Huang-Pan (6.2)
  (`Examples/CoppersmithWinogradEasyRectangular{Hashing,Rate,Bound}.lean`,
  `MatrixMultiplication/Rectangular{Bini,AsymptoticSum}.lean`); the sharp (6.1) for `r ≥ 1` is **DONE** too
  (`…EasyRectangularSharpBound.lean`, with `ω(1,1,2) < 3.3399`), via the type-class-restricted
  leg-fiber bound, since the pipeline's whole-fiber
  competitor bound is first-order sharp only for `r ≤ 1` (which gives (6.2)).
* **M-R6/M-R7** — **DONE**: the `r`-parameterized easy-CW and CW-Eq.(10) clients — Huang–Pan
  (6.1)/(6.2), then (7.1) and `ω(1,1,2) < 3.334` plus `ω < 2.3872`
  (`Examples/CoppersmithWinogradRectangular*.lean`). (7.2), the `r ≤ 1` branch, is **DONE** too; still open from §7 is
  (7.3), which needs a three-parameter client.  Sanity anchors: at `r = 1` each must reduce to the
  existing `easyCW_omega_le_log` and `cwFirstPower_base_inequality`.
* **M-R8** (a program, not a milestone): Coppersmith 1997's `α > 0.294`, which needs mixed tensor
  powers of `C₇` and `C₆` in one construction plus a four-parameter type selection.
* **M-R9** — **DONE** (`MatrixMultiplication/RectangularExponentThree.lean`): the three-parameter
  exponent, with symmetry, homogeneity, the information bound, the exact product law and
  Theorem 8.1. Huang–Pan (6.3)/(7.3) remain open, as the three-parameter analogue of the `f(r)`
  non-goal already recorded for M-R1.
* Out of scope: 1982's `O(N²log²N)` refinement (not expressible in `polynomialExponent`) and
  Huang–Pan Part II (§9–§11 applications).

### Assembly lesson from M-R6b (2026-08-28)

The planned "compress the extracted direct sum at `⟨1,F,1⟩`" step is **wrong** and must not be
re-proposed: it yields `ω(1,1,r+log_q t) ≤ (2+r)·log_q(q+2)`, which is exactly the blocking
consequence `rectangularOmega_le_omega_add_sub_one` of the square theorem, with the copy count
cancelling — nothing new is proved (checked numerically: at `q = 8, r = 1` the route gives
`ω(1,1,1.9186) ≤ 3.3219`, i.e. `easyCW`'s `2.4036 + 0.9186` on the nose). What is required is
Schönhage's device: compress at a near-optimal **rectangular** algorithm `⟨Q,Q,⌈Q^κ⌉⟩` whose rank
comes from an admissible exponent `τ > ω(1,1,κ)`, then let `τ ↓ ω(1,1,κ)`. The argument is
self-referential; `MatrixMultiplication/RectangularAsymptoticSum.lean` isolates it, and
`RectangularBini.lean` supplies the `Nat.clog`-density packager
`rectangularOmega_le_log_of_borderRankLE`, which needs a single certificate rather than a covering
family and supersedes `rectangularOmega_le_of_certificates` for clients of this shape.

### Rectangular program status after M-R7 (2026-08-28)

Proved: Coppersmith's `α ≥ 2 log 2/(5 log 5)`; Huang–Pan (6.1)/(6.2) on the easy tensor with
`ω(1,1,2) < 3.3399`; (7.1) on the full CW tensor with `ω(1,1,2) < 3.334` and `ω < 2.3872`; the
two interpolation theorems of §8.1; and the three-parameter exponent with Theorem 8.1 and the
exact value `ω(α,1,r) = r+1`.

Open, in rough order of value: **M-R8**, Coppersmith 1997's `α > 0.294` (needs mixed tensor
powers of `C₇` and `C₆` in one construction plus a four-parameter type selection — a program, not
a milestone); Huang–Pan (7.2) and (7.3); §8.1's crossing-point analysis at `r ≈ 1.171`; and the
promotion cleanups (the duplicated method-of-types envelope now that
`Analysis/BinomialEntropyEnvelope.lean` exists, and `log 11` into `Analysis/LogConstants.lean`).

### M-R8 stage 1 finding: the paper's mixture is `9a` and `8b` with `a`, `b` independent

Coppersmith 1997's §4 line reads "Take the tensor product of `9 ` copies of construction `  ` and
`8 ` copies of `  `" — the italic letters are Type-3 bitmaps and do not extract, so `9r + 8r` and
`9a + 8b` render identically. The scoping pass read it as `9r`/`8r`; the numerics say otherwise.
The construction's achievable exponent is the fixed point `α = log P / log M` of the
self-referential compression (the non-self-referential packing gives only `0.2053`), maximized
subject to the paper's own "number of y-blocks approximately equal to the number of x-blocks":

| reading | `α` |
| --- | --- |
| `9r`, `8r` (i.e. `a = b`) | 0.2944039 |
| ratio fixed at `a : b = 9 : 8` | 0.2945070 |
| **`9a`, `8b`, `a` and `b` free** | **0.294628905** at `a/b = 1.5584`, `s/a = 0.010139`, `t/b = 0.014494` |

Theorem 1 states `α = 0.29462…`, so only the free-ratio reading reproduces the paper, and it does
so to six digits. Corroborating prose on p. 45: "We have chosen `_`, `_`, `_`, and `_` to make the
number of y-blocks approximately equal to the number of x-blocks" — **four** quantities, i.e.
`a, b, s, t`; with `9r`/`8r` only two are free. So the ratio `a : b` is one of the four parameters
of the "four-parameter type selection", not a constant.

Stage-2/3 plan (also in the module docstring): reusable unchanged are
`RectangularAsymptoticSum.lean`'s bootstrap — load-bearing here, not optional, since naive packing
gives 0.2053 — `RectangularBini.lean`'s single-certificate packager, the envelope
parameterization of `cwRect_master_inequality_of_fiberGrowth`, and `BinomialEntropyEnvelope.lean`
used twice multiplicatively. New work, in order: (1) generalize the hashing input from a power of
one tensor to a `PartitionedTensor` external product, since Coppersmith's weights run over all
`9a + 8b` positions; (2) two-sided leg selection — the competitor count is a product of two
`cwRectLegTypedFiber`s and the *same* leg must be chosen on both halves, while Coppersmith's
parameters put the two halves in different Huang–Pan regimes, so neither one-sided hypothesis set
applies; (3) the near-equality `R ≤ N·M^{2+ε}`, the only place §3's `q+2 = q+2` remark is used and
the reason any `(a,b)` is admissible; (4) the numeric optimization. **Hardest expected
obstruction:** the duplicate-pruning step of p. 47 over a two-region position set — the
compatibility-zeroing modules are phrased for block addresses that are words over one alphabet,
while a mixed power has addresses that are *pairs* of words with coordinatewise compatibility on
both halves. Same combinatorics, wide refactor, and it touches modules the M-R6/M-R7 wave just
consolidated — hence a milestone of its own.

## Alman–Li (arXiv:2605.21738) §§5–7: inventory and verdict (2026-08-28)

Proved: Theorem 5.1 and Corollary 5.1 (`Tensor/FreeLunchSpeedup.lean`). **No function-field or
two-parameter degeneration layer is needed** for anything in scope — scoped, then deliberately not
built. The paper's second parameter exists only because it treats the input as an opaque
restriction of `F(λ)`-tensors with unknown junk-block orders; here the orders are explicit
(`HasLeadingTerm`), so shifting the block families by `(0,0,d+d'+2)` and `(d+1,d+1,0)` puts both
diagonal blocks at degree `2d+d'+2` and every junk block strictly above.

**Update 2026-08-27.** (1) and Proposition 5.3 are **done**.

* **Two-legged rank interface — DONE** (`Tensor/MatrixFlattening.lean`,
  `MatrixMultiplication/OneSliceNormalForm.lean`). The `Z`-leg-is-`K` leg family was evaluated and
  *rejected*: a `Leg`-match family forces `cases`-built instances (a `Leg.rec` inside every
  algebraic diamond) and a single universe for all three legs. Adopted instead: no new tensor
  space at all — a "two-legged tensor" is a `Tensor3` plus a functional `ζ` on its `Z` leg, read
  as `matrixFlatten ζ S : (V .Y)ᵛ →ₗ[K] V .X`, with `matrixRank` its `finrank` of range. One
  structure theorem (`map_ofLegs_eq_sum_pure_of_flatten`) yields everything: `rank ≤ min dim`, the
  rank-drop bound `matrixRank_le_add_of_map`, and both directions of the `⟨1,t,1⟩` identification.
* **Proposition 5.3 — DONE** as `polynomialDegenerates_directSum_oneSlice`
  (`MatrixMultiplication/OneSliceSpeedup.lean`), stated composed with Theorem 5.1:
  `S ⊵ T ⊕ ⟨1, r − n − m, 1⟩`. The maximal `A'`, `B'` are built as aggregate coordinate maps of
  `range (φ ∘ Bᵛ)` and `ker (A ∘ φ)`. The `s = n` clause of Theorem 6.1 is **verified**
  unconditional: it is exactly `matrixRank_le_finrank_X`/`_Y`.

**Update 2026-08-27 (second pass).** Proposition 5.4 and the restriction half of Theorem 6.1 are
**done**.

* **Proposition 5.4 — DONE** as `exists_oneSliceAppend`
  (`MatrixMultiplication/OneSliceAppend.lean`), together with its composition with Proposition 5.3,
  `polynomialDegenerates_directSum_oneSliceAppend`. Two corrections to the previous plan:
  * the factorization `M = (A₁ ⊗ B₁)⟨1,s,1⟩` is **not** obtainable from
    `restricts_matrixMultiplication_matrixRank`: that theorem's size parameter is the ambient
    `matrixRank ζ S = q`, not `rank M`, and its target family would have to have `Z` component
    `K`. It was proved directly at the flattening level as `exists_oneSlice_factorization`
    (basis of `range M`, plus reflexivity of the finite-dimensional `Y` leg to turn the
    coefficient functionals on `(V .Y)ᵛ` into vectors of `V .Y`);
  * the paper fixes `s = rank M`; the proved version takes any `s ≥ rank M`, and this padding
    **cannot** be deferred to a source restriction afterwards, because a larger `s` also enlarges
    the extracted summand `⟨1, q + s − 2n, 1⟩`.
  The direct-sum bookkeeping is `Tensor.matrixRank_directSum`
  (`Tensor/MatrixFlatteningDirectSum.lean`): the contracted slice of a direct sum is block
  diagonal, so its rank is additive. `matrixFlatten` also gained `matrixFlatten_zero` and
  `matrixFlatten_finset_sum`.
* **Theorem 6.1, restriction form — DONE** as
  `polynomialDegenerates_diagonalTensor_directSum_oneSlice` and its `s = n` clause
  `polynomialDegenerates_diagonalTensor_oneSlice_of_rankLE`
  (`MatrixMultiplication/NonminimalRankSpeedup.lean`). The source `⟨r⟩` is the library's existing
  `Tensor.diagonalTensor K (Fin r)`, **not** the `matrixMultiplicationDirectSum` reading: the
  coordinate diagonal makes `matrixRank (coordinateSum K (Fin r)) ⟨r⟩ = r` a three-line
  computation, while the indexed direct sum would have required `IndexedDirectSumSpace`
  flattening bookkeeping for no gain. Fixing the contraction to the all-ones functional loses no
  generality (rescale `aᵢ ↦ c'ᵢaᵢ`, `cᵢ ↦ c'ᵢ⁻¹cᵢ`). `NonminimalBorderRankSpeedup` was restated
  against `diagonalTensor` and given explicit `FiniteDimensional` hypotheses, so that the
  remaining gap to the proved theorem is exactly `RankLE → BorderRankLE`; its `n ≤ r` hypothesis
  was dropped as unnecessary.

Remaining, in dependency order:
1. **Theorem 6.1 for border rank** (`NonminimalBorderRankSpeedup`) — **DONE 2026-10-07**
   (`MatrixMultiplication/NonminimalBorderRankSpeedup.lean`,
   `AlmanLi.nonminimalBorderRankSpeedup`). The earlier verdict here — "needs a scalar extension
   of the tensor layer to `RatFunc K` plus a descent; scoped and deliberately not built" — was
   wrong about what is needed, and must not be re-proposed. No base change is involved. The
   polynomial free-lunch theorem is applied to two explicit polynomial families on
   `⟨r⟩ ⊕ ⟨1,n,1⟩`: `F` carries the certificate and sends the slice to `−∑ᵢ B_{ji} aᵢ`, `v_j`, `0`;
   `G` sends `eᵢ` to `(αᵢ, δᵢ, z')`. The mixed blocks vanish because the slice cancels the
   `Y`-expansion and because `P·δ = 0`, and the pure `G` block is `q·⟨1,r−n,1⟩` because
   `αᵀ·δ = q·1`. The pair `(δ, α)` is a *kernel frame* of the polynomial coordinate matrix `P` of
   the certificate (`Tensor/PolynomialKernelFrame.lean`): rank–nullity over the fraction field of
   `K[X]`, a left inverse, and cleared denominators. The `s = n` clause needs no rank hypothesis
   because an `n × n` polynomial matrix factors through its columns; the general-`s` border form
   (`s ≥` the rank of `M` over `F(λ)`) is not proved and would need a rank factorization of a
   polynomial matrix, i.e. a second kernel frame.
   The core (`Tensor.polynomialDegenerates_oneSliceFrameTensor_directSum`) is already **grouped**:
   `p` groups of at least `m + n` certificate terms give `p ⊙ ⟨1,m,1⟩`, with ungrouped terms
   allowed, so Theorem 6.3 in its border-rank form needs only the presentation bookkeeping below.
2. **Proposition 5.7** (`OneSliceCompression`, p. 18) — independent of everything else; needs
   `exists_linearIndependent'` on the `X`-basis family of `⊕_i ⟨1,n_i,1⟩`, a per-block increasing
   enumeration of the chosen subset, and a left inverse over a field. Unblocks the second proof of
   Theorem 6.3. Largest index-bookkeeping cost is `IndexedDirectSumSpace` coordinates; still the
   largest single item in this section.
3. **Theorem 6.3** (p. 21) — **DONE 2026-10-07**, in border-rank form
   (`MatrixMultiplication/GroupedBorderRankSpeedup.lean`, `AlmanLi.groupedOneSliceSpeedup`).
   Groupwise application of Theorem 6.1 does *not* work for a border certificate: the group sums
   are polynomial tensors with no leading term of their own, which is why the core of item 1 is
   grouped from the start. The file adds only bookkeeping: the indexed-direct-sum source
   restricts onto the framed source in standard coordinates (no `DFinsupp` basis is needed —
   `indexedFoldMap` does it), the grouping is `i ↦ ⌊i / 3n⌋` with the leftover terms ungrouped,
   and `n = 0`, where `finrank = 0` gives no basis, goes through the span form of the core with
   every term ungrouped. It does not need Proposition 5.7.
4. **Theorem 7.3** (`DirectSumIdentity`, p. 29) — independent; needs only the restriction form
   already proved plus explicit coordinate maps. No new theory.
5. Out of scope, unchanged: Theorem 6.2, Corollary 6.1, and all of §7.1/§7.2 — they need
   Proposition 4.5 and Strassen duality.

### M-R8 stage 2 landed, and stage 1's two predicted obstructions were both wrong (2026-08-28)

`Examples/CoppersmithMixedPower{Hashing,Rate}.lean` produce `RectangularScheduleExtraction` for the
mixed power and instantiate the shared schedule. **No existing file changed** — no declaration was
renamed, restated or generalized anywhere in the hashing or zeroing layers.

Stage 1 predicted (i) generalizing the hashing input from a power to an external product and
(ii) a wide refactor of the zeroing layer for pair-of-words addresses, calling the second "the
hardest expected obstruction". Both were unnecessary:

* The hashing layer is already generic. `PartitionHashEncoding` is a structure over a support
  finset with an injective encoding and a constant-sum legality; it mentions no tensor, and
  `modeledTargets_to_legwiseIsolatedIndexedDirectSum` consumes an arbitrary `PartitionedTensor`
  whose support matches the modeled targets. Nothing in the chain sees a power.
* Pairs of words *are* words. `cwPartitionedTensor K 7` and `cwPartitionedTensor K 6` share the
  block-label family and the support `cwBlockSupport`; only the block spaces differ. So the
  mixed power reindexes along `positiveWordAppendEquiv` into a genuine word of length
  `(n₇+1)+(n₆+1)` over `CWBlock`. Faithfulness: the map is an `Equiv`, so no address is created,
  merged or lost; the block spaces transport by the identity, so constituents are unchanged.
  Coppersmith's p. 47 pruning is then literally the single-alphabet pruning already formalized.

**The real obstruction was the competitor count.** A concatenated mixed word has a joint type on
the common alphabet, but that type also admits words trading letters between the two halves, so
the type-theoretic bound `card_legFiber_legalTargets_le_card_typedWordMapFiber` gives the fiber at
the *summed* profile — exponentially larger than the truth, and fatal to the rate. The fix is
positional: `card_legFiber_legalTargets_eq_card_sourceWordLegFiber` is a public **equality**
already stated for an arbitrary source-word family, and chaining it with the leg fiber of a
concatenated family yields exactly the product of the two halves' fibers. That chain is the only
genuinely new mathematical content of stage 2.

Stage 1's "two-sided leg selection" also did not arise: the fiber bound is a max over legs of a
*product*, so the same leg is automatically chosen on both halves.

**Stage 3 is arithmetic and numerics only**, nothing structural: (1) a geometric envelope `Φ` with
`fiber(N) ≤ Φ^N`, a product of two single-`q` envelopes whose attaining leg is decided per half by
the Schur comparisons (at Coppersmith's parameters both halves give the `y` leg); (2) a choice of
`κ` — the optimum `log C / log A` is irrational, hence the open parameter; (3) instantiating the
four-parameter selection `(2(u−s), 7u, s, 2u)` and `(v−2t, 3v, t, v)` from stage 1, giving
`R = 9^{18u}·8^{8v}`, `A = 7^{7u}6^{3v}`, `C = 7^{2(u−s)}6^{v−2t}`; (4) the near-equality
`R ≤ N·M^{2+ε}`, a two-factor maximal-multinomial-term estimate, still unformalized and
independent of the rest; (5) the numeric optimization and the `α > 0.294` endpoint through
`rectangularOmega_le_log_of_borderRankLE`.

## The rectangular program is complete (2026-08-28)

All three rectangular papers are formalized. Coppersmith 1982 (`α ≥ 2 log 2/(5 log 5)`),
Huang–Pan 1998 (§§2–3, 5–8: (6.1), (6.2), (7.1), (7.2), `ω(1,1,2) < 3.334`, the two interpolation
theorems, the three-parameter exponent and Theorem 8.1), and now **Coppersmith 1997, `α > 0.294`**
(`Examples/CoppersmithRectangular1997.lean`, `κ = 5/17`, parameters `(u,s,v,t) = (21,1,47,1)`).

Two corrections from stage 3, both verified numerically rather than assumed:

* **Neither half of the mixed construction satisfies a Schur leg hypothesis.** At Coppersmith's
  parameters the left half's `x` leg dominates by `e^{11.05}`, the right half's `y` leg by
  `e^{8.39}`, and the *product*'s `x` leg by `e^{2.66}`. The leg choice cannot be made per half;
  it is made once, multiplicatively, through the envelope cancellations `E/Φ_x` and `E/Φ_y` as
  ternary entropy bases. Their near-equality is the paper's p. 45 balancing sentence, and at the
  continuous optimum they are exactly equal.
* **`R ≤ N·M^{2+ε}` is an exact identity, not an estimate**: `(E/Φ)·A² = R`, from
  `378^378·7^294 = 9^378·42^42·294^294·42^42` and `376^376·6^282 = 8^376·47^47·282^282·47^47`.
  Coppersmith's §3 remark that the construction has `q+2` multiplications and `q+2` x-variables
  *is* this identity; his `ε` is the Stirling loss the schedule already absorbs, so the master
  inequality collapses to `A^ω ≤ A²` with no slack.

Left open, none of it needed for the theorems: Huang–Pan (7.3) (three-parameter, needs a
three-parameter client); §8.1's crossing point at `r ≈ 1.171`; and sharpening `κ` from `5/17`
(0.294118) toward the construction's true `0.2946289` — the next admissible pairs are
`(23,1,48,1)`, `(24,1,49,1)`, `(27,1,51,1)` reaching `κ_max = 0.294405`, and a rational near
`0.2946` would need a ~350 000-digit integer comparison. Also: the `(E/Φ)·A² = R` identity is
currently proved only at the numeric instance; its general two-line form would let the endpoint be
parameterized by `(u,s,v,t)`.

