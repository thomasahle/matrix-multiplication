# Matrix-multiplication tensor formalization

[![CI](https://github.com/thomasahle/matrix-multiplication/actions/workflows/ci.yml/badge.svg)](https://github.com/thomasahle/matrix-multiplication/actions/workflows/ci.yml)

A Lean 4 / Mathlib formalization of the theory of fast matrix multiplication, from Strassen to the
Coppersmith–Winograd method and its modern refinements, together with the lower bounds and
barrier results that limit those methods. Highlights, each a kernel-checked theorem:

- **`ω < 2.374631`** — Duan–Wu–Zhou's second-power bound on `CW_6^{⊗2}` (arXiv:2210.10173,
  §6.3), proved unconditionally over any field following the paper's argument
  (`omega_lt_2374631`). The paper's headline `2.371866`, from higher powers, is not formalized.
- **The classical upper-bound line** — Strassen's `R⟨2,2,2⟩ ≤ 7`, Laderman, Bini's `ω < 2.695`,
  Schönhage's asymptotic sum inequality and `ω < 2.6`, and the Coppersmith–Winograd bounds
  `ω < 2.3872` and `ω < 2.375477`.
- **Lower bounds** — `rank ⟨2,2,2⟩ = 7`, the substitution method, Koszul flattenings, slice rank
  and subrank.
- **Barriers** — Alman–Vassilevska Williams' Theorem 7.1 (a universal `c > 2` with
  `ω_g^coord(CW_q^σ) ≥ c` for every generalized CW tensor) and Alman's universal-method barrier
  `ω_u(CW_q^σ) ≥ 13/6`.

No `sorry`, no project axioms: CI runs an enforcing `#assert_axioms` audit over the results, which
allows only `propext`, `Classical.choice` and `Quot.sound` (the few results without an assertion say
so in the tables). No new bound on `ω` is claimed. The repository is substantially AI-built —
written largely by AI agents working under human direction, with the author reviewing and taking
responsibility; see [`CONTRIBUTING.md`](CONTRIBUTING.md) §5 for what that means and how the trust
checks account for it. The `## Results` section below indexes everything proved, with sources and
hypotheses.

This repository is developing a reusable Lean 4 library for algebraic-complexity tensors, with two
downstream applications: the Duan–Wu–Zhou second-power (level-two) development (the published
`ω < 2.374631` endpoint) and the conditional Total-Weight framework, whose manuscript is in
preparation and not yet public, and which claims no improved bound. The reusable library contains
no paper-certificate tables or optimizer-specific definitions.

Coverage runs in both directions. The upper-bound side goes from Strassen through Schönhage,
Bini, and the classical Coppersmith--Winograd analyses to the Duan–Wu–Zhou second-power analysis
and the conditional Total-Weight framework, whose archived certificate does not satisfy the
framework's uniform-quotient hypothesis and so yields no bound.
The lower-bound side covers the substitution method, Koszul flattenings, slice rank and subrank,
the Alman--Vassilevska Williams barrier framework of arXiv:1810.08671, whose headline
Theorem 7.1 is now proved in full, and Alman's universal method, whose Theorem 5.7 barrier
`ω_u(CW_q^σ) ≥ 13/6` is proved unconditionally. The `## Results` section below is the single consolidated index
of everything proved here; `DESIGN.md` holds the results ladder, `LOWER_BOUNDS_ROADMAP.md` the
lower-bound inventory, and `BARRIER_FRAMEWORK.md` the dependency-ordered milestone list for the
barrier program.

The current tree builds without `sorry`, `admit`, or project axioms.

The cited papers (`papers/`) are not distributed with the repository. A docstring that cites
`papers/sources/<arxiv-id>/<file>.tex:<lines>` refers to the arXiv source of that paper, and one
that cites another file under `papers/` refers to a local copy or transcription of the paper cited
next to it. A docstring that cites `better_bound/paper.tex` or another `better_bound/` file refers
to the Total-Weight manuscript and its working notes, which are not part of this release.

## Results

One consolidated index of what is *proved and machine-checked here*, grouped by theme. Every
declaration below exists in the tree today; module paths are relative to `AlgebraicComplexity/`
except where a row marks one *(repository root)*, which is the top-level paper library — the
named-obligation and conditional-endpoint tables' `MatrixMultiplication/` paths are all of that
second kind. Each of these results is
also covered by the enforcing axiom audit, which the `AxiomAudit` target runs over its whole
`AxiomAudit.*` glob: **1483 `#assert_axioms` checks** in `AxiomAudit.lean` itself and 5205 more
across the 775 focused modules under `AxiomAudit/`, with a further 12 in
`AxiomAuditCertificate.lean` and 5445 across `AxiomAuditCertificate/`; a passing
audit means the only axioms used are `propext`, `Classical.choice`, and `Quot.sound`. A
theorem below that carries no `#assert_axioms` line anywhere says so in its own status cell, and
so do the rows covered only by the opt-in `AxiomAuditCertificate` target.

Two conventions in the "Hypotheses / status" column: *unconditional* means no proof obligation
and no paper-specific assumption, and a *named proof obligation* is an unproved deep input carried
as an explicit `Prop` hypothesis (never an `axiom`) — the ones the tables above depend on are
collected in the last table. *Unconditional* is written only for a statement with no data-carrying
binder; a theorem whose conclusion rests on a supplied datum, certificate or `Prop` says which one.
Conditional `ω < …` endpoints are **not** results and are not in these tables: they are inventoried
separately in "Conditional endpoints (not results)" at the end of this section.

### Upper bounds: explicit algorithms and exponent bounds

| Result | Source | Lean declaration | Module | Hypotheses / status |
| --- | --- | --- | --- | --- |
| `R⟨2,2,2⟩ ≤ 7`, and `R⟨2^k,2^k,2^k⟩ ≤ 7^k` | Strassen 1969 | `strassen_rankLE`, `strassen_rankLE_pow` | `Examples/Strassen.lean` | any `CommRing`; closed integer coefficient certificate |
| `ω ≤ log 7 / log 2` | Strassen 1969 | `strassen_omega_le_log` | `Examples/Strassen.lean` | any `CommRing`, unconditional |
| `R⟨3,3,3⟩ ≤ 23`, hence `ω ≤ log 23 / log 3` | Laderman 1976 | `laderman_rankLE`, `laderman_omega_le_log` | `Examples/Laderman.lean` | any `CommRing`, kernel-checked certificate |
| `R⟨2,2,3⟩ ≤ 11` (= the paper's `⌈(3·2·3+3)/2⌉`) | Hopcroft–Kerr 1971, Theorem 1 at `p = 2, n = 3` | `HopcroftKerr.rankLE_two_two_three`, `HopcroftKerr.rankLE_count` | `Examples/HopcroftKerrUpper.lean` | any `CommRing`; the general `(p,n)` case is not claimed |
| `R⟨3,2,3⟩ ≤ 15`, `R⟨3,3,3⟩ ≤ 23` in characteristic two | machine-discovered in this repository by flip-graph search (no external factor table) | `DiscoveredDecompositions.rankLE_three_two_three`, `DiscoveredDecompositions.rankLE_three_three_three` | `Examples/DiscoveredDecompositions.lean` | `CommRing` with `2 = 0`; `ZMod 2` instances also proved |
| Bini's five-term approximate `2×2` partial product; `ω < 2.695` | Bini–Capovani–Romani–Lotti 1979, via Schönhage's partial τ-theorem | `bini_omega_lt` | `Examples/Bini.lean` | any **infinite** field, unconditional |
| Schönhage's ten-term degeneration of `⟨3,1,3⟩ ⊕ ⟨1,4,1⟩`; `9^(ω/3) + 4^(ω/3) ≤ 10`; `ω < 2.6` | Schönhage 1981 (notes Section 3.3) | `schonhage_borderRankLE`, `schonhage_asymptoticSum_bound`, `schonhage_omega_lt_two_point_six` | `Examples/Schonhage.lean` | any `CommRing` for the certificate, any field for the asymptotic-sum bound and `ω < 2.6`; unconditional |
| Schönhage's *second design* partial product (`k = q = 2`): `R̲₂⟨partial 2×3 · 3×2⟩ ≤ 5`, hence `ω ≤ 3 log 5 / log 6 < 2.695` | Schönhage 1981, §5, eqs. (5.5)–(5.8) p. 446; = Coppersmith 1982 p. 467's displayed identity | `sd_borderRankLEAt`, `sd_omega_lt`, `card_pmmSupport_secondDesign` | `Examples/SchonhageSecondDesign.lean` | any `CommRing` for the certificate, infinite field for `ω`; the counting lemmas are proved for all `(k,q)` with `k ≥ 1`, the general certificate is stated in the module doc |
| `R̲(CW_q) ≤ q + 2` | Coppersmith–Winograd 1990 | `coppersmithWinograd_borderRankLE` | `Examples/CoppersmithWinograd.lean` | any `CommRing`; explicit `q+2` polynomial pure tensors |
| `R̲(CW_q^σ) ≤ q + 2` for the classical member `σ = id` | AVW 2018, Definition 3.1 | `genCW_borderRankLE_refl` | `Examples/GeneralizedCoppersmithWinogradBorderRank.lean` | any `CommRing`; **deliberately not claimed for general `σ`** — see the errata below |
| `(27/4)·q^ω ≤ (q+2)^3`, i.e. `ω ≤ f(q) = log_q(4(q+2)³/27)` | Coppersmith–Winograd 1990 §6 (Cornell CS 6810 notes, Theorem 4.1) | `easyCW_base_inequality`, `easyCW_omega_le_log` | `Examples/CoppersmithWinogradEasyHashing.lean` | any field; `q > 0` for the product inequality and `q > 1` for the logarithmic form; parametric in `q` |
| `ω < 2.41` (easy CW, `q = 8`) | Cornell CS 6810 notes, Theorem 4.1 | `coppersmithWinograd_easy_omega_lt`, `easyCWTarget_eq_decimal` | `Examples/CoppersmithWinogradEasyHashing.lean` | any field, unconditional; one exact-rational atanh certificate, no floating point |
| `ω < 2.3872` (first-power `CW_6`) | Coppersmith–Winograd 1990 §7 (notes Theorem 4.2) | `coppersmithWinograd_firstPower_omega_lt`, `cwFirstPowerTarget_eq_decimal`, `cwFirstPower_base_inequality` | `Examples/CoppersmithWinogradFirstPower{,Hashing}.lean` | any field, unconditional; twenty exact rational atanh terms |

### Upper-bound machinery (reusable)

| Result | Source | Lean declaration | Module | Hypotheses / status |
| --- | --- | --- | --- | --- |
| Schönhage's asymptotic sum inequality: `∑ (m_i n_i p_i)^(ω/3) ≤ R̃(T)` for a degeneration to a direct sum of positive rectangular tensors | Schönhage 1981, Theorem 7.1 (notes Theorem 3.7) | `asymptoticSumInequality` | `MatrixMultiplication/AsymptoticSum.lean` | any field; **no** rank-additivity conjecture assumed |
| Schönhage's partial τ-theorem for genuinely partial matrix products | Schönhage 1981, Theorem 4.1 | `omega_le_of_borderRankLE_partialMatrixMultiplication` | `MatrixMultiplication/PartialAsymptoticSum.lean` | any **infinite** field; a pattern whose every inner index is used on both sides, with `f ≥ 2` support cells and border rank `l ≥ 1` |
| `ω ≤ log r / log q` from `RankLE r ⟨q,q,q⟩`, and the rectangular `(mnp)^(ω/3)` form | notes Proposition 2.1 / Theorem 2.12 | `omega_le_log_of_rankLE`, `matrixMultiplication_volume_rpow_omega_div_three_le_of_rankLE` | `MatrixMultiplication/Exponent.lean` | any `CommSemiring`; `q > 1` and `r ≥ 1` for the square form, positive `m, n, p` and `r ≥ 1` for the rectangular one |
| `2 ≤ ω ≤ 3` | folklore sanity bound | `two_le_omega`, `omega_le_three` | `MatrixMultiplication/Exponent.lean` | `2 ≤ ω` needs a field |
| Bilinear algorithms of length `r` ⟺ rank-`r` tensor decompositions, specialized to matrix multiplication | notes Definitions 2.2–2.4, Fact 2.9 | `rankLE_coeffTensor_iff_exists_computes`, `matrixMultiplication_rankLE_iff_exists_algorithm` | `MatrixMultiplication/BilinearAlgorithm.lean` | any `CommSemiring`, both directions |
| Conciseness: `max` leg dimension bounds tensor rank | notes Lemma 2.6 | `RankLE.max_finrank_le` | `Tensor/Concise.lean` | any field; basis-free, via dual contractions |
| Recursive block compilation of a rank certificate into straight-line programs with exact operation counts | notes Proposition 2.7, forward direction | `omega_le_and_exists_straightline_of_rankLE`, `exists_straightline_matrixProduct_of_omega_lt` | `MatrixMultiplication/RankComplexityRecursion.lean` | any `CommSemiring` for the certificate form, which needs `q > 1` and `q² < r`; the exponent-level form is over a field and produces an existential constant; forward direction; the converse is the next row |
| **Strassen's converse: a straight-line program with `M` multiplication gates computing a bilinear map gives a bilinear algorithm of length at most `2M`**; hence `R(⟨m,n,p⟩) ≤ 2 · mulOps` for every program computing the matrix product, programs with `O(n^τ)` multiplications force `ω ≤ τ`, and **`ω ≤ τ` iff the `n × n` product has straight-line programs of size `O(n^(τ+ε))` for every `ε > 0`** | notes Proposition 2.7, converse direction and the full equivalence (Strassen 1973) | `exists_bilinearAlgorithm_of_straightline`, `rankLE_matrixMultiplication_of_straightline`, `omega_le_of_straightline`, `omega_le_iff_exists_straightline`, `Straightline.exists_bilSpan`, `Trunc.bil_mul`, `Straightline.eval_mapCoeff` | `MatrixMultiplication/RankComplexityConverse.lean` | any **infinite** field (the program is only assumed correct on points of the field, so polynomial identity needs infinitely many of them); `τ ≥ 0` for the exponent forms. The proof truncates every register to degree `≤ 1` in each input block inside the iterated trivial square-zero extension `Trunc K ι κ`, where each multiplication gate adds two rank-one matrices to the span of the bilinear parts and no other gate adds any. Scalar multiplications by constants are free, as in the source. Asserted in `AxiomAudit/RankComplexityConverse.lean` |
| Rectangular exponent `ω(κ)`: monotone, convex, `ω(1) = ω`, `ω(0) = 2`, interpolation `ω(κ) ≤ κω + 2(1−κ)` | Coppersmith / Lotti–Romani lineage | `rectangularOmega_one`, `rectangularOmega_zero`, `rectangularOmega_convexOn`, `rectangularOmega_le_interpolation` | `MatrixMultiplication/RectangularExponent.lean`, `RectangularInterpolation.lean` | any `CommSemiring` for monotonicity, `ω(1) = ω`, convexity and interpolation (the last for `0 ≤ κ ≤ 1`); `ω(0) = 2` needs a field |
| The dual exponent `α`, with `α = 1 ↔ ω = 2` | Coppersmith 1997 | `rectangularAlpha`, `rectangularAlpha_eq_one_iff_omega_eq_two` | `MatrixMultiplication/RectangularExponent.lean`, `RectangularInterpolation.lean` | any field |
| The three-parameter exponent `ω(a,b,c)`: symmetry, homogeneity, the information bound `max(a+b,b+c,c+a) ≤ ω(a,b,c)`, the subadditive product law `ω(a₁+a₂,b₁+b₂,c₁+c₂) ≤ ω(a₁,b₁,c₁) + ω(a₂,b₂,c₂)` with no rounding loss, Theorem 8.1, and the exact value `ω(α,1,r) = r+1` for `r ≥ 1` | Huang–Pan 1998, §2 p. 262 and Theorem 8.1 p. 281 | `generalRectangularOmega`, `generalRectangularOmega_smul`, `max_le_generalRectangularOmega`, `generalRectangularOmega_add_le`, `rectangularOmegaThree_le_huangPan_low/_high`, `rectangularOmegaThree_rectangularAlpha` | `MatrixMultiplication/RectangularExponentThree.lean` | fields — both Theorem 8.1 branches go through `rectangularOmega_rectangularAlpha`, and the second also needs `α < 1`, `α ≤ t ≤ 1`, `r ≥ 1`; the bound `≤ r+1` is shown to fail for `r < t` (`lt_rectangularOmegaThree_of_lt`), so their standing lower bound on `r` cannot simply be dropped |
| **`α ≥ 2 log 2 / (5 log 5) = 0.1722704…`, hence `17/100 < α` and `ω(κ) = 2` for `κ ≤ α`** — multiplying `N × N` by `N × N^α` costs `N^(2+o(1))` | Coppersmith 1982, SIAM J. Comput. 11(3) 467–471, Theorem p. 467 | `coppersmith1982_rectangularAlpha_ge`, `coppersmith1982_rectangularOmega_eq_two`, `coppersmith1982_alpha_gt_seventeen_hundredths` | `Examples/CoppersmithRectangular1982.lean`, `…1982Certificate.lean` | any **infinite** field, unconditional; `17/100 < α` reduces to the exact integer comparison `5^85 < 2^200` |
| **`α > 0.294`** — `N × N` by `N × N^{0.294}` in `N^{2+ε}` | Coppersmith 1997, J. Complexity 13 42–49, Theorem 1 p. 48 | `coppersmith1997_alpha_gt`, `coppersmith1997_rectangularAlpha_ge`, `cop97_entropy_div_growth` | `Examples/CoppersmithRectangular1997.lean`, `CoppersmithMixedPower{Type,Hashing,Rate}.lean` | any field, unconditional; every side condition is an exact integer comparison, and the paper's `R ≤ N·M^{2+ε}` is proved to be an exact identity rather than an estimate |
| `ω(1,1,r) ≤ log(4·r^r·(q+2)^{2+r}/(2+r)^{2+r})/log q` for rational `0 ≤ r ≤ 1`, and the `2^{1+r}` form for rational `r ≥ 1` | Huang–Pan 1998, J. Complexity 14, (6.2) p. 274 (the `r ≤ 1` branch is theirs verbatim) | `huangPan_rectangularOmega_le_of_le_one`, `huangPan_rectangularOmega_le_of_one_le`, `easyRect_master_inequality` | `Examples/CoppersmithWinogradEasyRectangular{Type,Hashing,Rate,Bound}.lean` | any field, unconditional; at `q = 8, r = 1/2` it gives `2.1667` against the interpolation bound's `2.2015`. the `r ≥ 1` branch is upgraded to the sharp (6.1) in the row below |
| **`ω(1,1,r) ≤ log((1+r)^{1+r}(q+2)^{2+r}/(2+r)^{2+r})/log q` for rational `r ≥ 1`, hence `ω(1,1,2) ≤ 7 log 3 / log 10 < 3.3399`** | Huang–Pan 1998, (6.1) p. 273 and §3 (3.6) p. 266 | `huangPan_rectangularOmega_le_of_one_le_sharp`, `huangPan_rectangularOmega_two_le_seven_log_three`, `huangPan_rectangularOmega_two_lt` | `Examples/CoppersmithWinogradEasyRectangularSharpBound.lean` | any field, unconditional; the `q = 10` optimum is exact (`27·12⁴/256 = 3⁷`), certified from the repo's ten-digit log enclosures |
| **`ω(1,1,2) < 3.334`** (Huang–Pan's headline) and `ω < 2.3872`, both from the `β`-refined rectangular client on the full CW tensor | Huang–Pan 1998, §5 p. 271 and (7.1) §7.1 p. 277; `f(1) = 2.38719`, `f(2) = 3.334` §8.1 p. 280 | `huangPan_fullTensor_rectangularOmega_le`, `cwRect_rectangularOmega_two_lt`, `cwRect_omega_lt`, `cwRectLegTypedFiber_X_le_Y` | `Examples/CoppersmithWinogradRectangular{Type,Hashing,Rate,Bound,HuangPan}.lean` | any field, unconditional; the paper's "select the larger" step is proved, not assumed, and the `r = 1` specialization recovers `cwFirstPower_base_inequality` |
| Huang–Pan (7.2), the `r ≤ 1` branch on the full CW tensor | Huang–Pan 1998, §7.2 pp. 277–278 | `huangPan_fullTensor_rectangularOmega_le_of_le_one`, `cwRectLegTypedFiber_Y_le_X`, `huangPan_fullTensor_bracket_one_eq` | `Examples/CoppersmithWinogradRectangular{Type,Bound,HuangPan}.lean` | any field; the same schedule at the X-leg fiber with the count comparison reversed, agreeing with (7.1) at `r = 1` both at the envelope and at the formula |
| Asymptotic rank: power law both halves, subadditive on `⊕`, submultiplicative on `⊗`, and `R̃⟨n,n,n⟩ = n^ω` | Strassen's asymptotic spectrum lineage | `asymptoticRank_power_eq`, `asymptoticRank_directSum_le`, `asymptoticRank_external_le`, `asymptoticRank_matrixMultiplication_eq_rpow_omega` | `Tensor/AsymptoticRank.lean`, `Tensor/AsymptoticRankCalculus.lean`, `MatrixMultiplication/AsymptoticRank.lean` | fields for the `n^ω` identity, which is stated for `n ≥ 1`; the power-law *equality* assumes that no tensor power of `T` vanishes (`∀ m, 1 ≤ R(T^{⊗m})`), while the `≤` half `asymptoticRank_power_le` is unconditional |
| Cube bound: three matrix-multiplication direct-sum degenerations force `R̃(T)³ ≤ r³ + 3r²s + 3rs² + s^ω` (duality-free) | Alman–Li 2026 (arXiv:2605.21738), Proposition 4.4 | `asymptoticRank_pow_three_le_of_matrixMultiplication_directSum_degenerations` | `Examples/AlmanLiSpeedup.lean` | any `CommSemiring`; needs `1 ≤ s` and `∀ j, 1 ≤ R(T^{⊗j})`. Proved without Strassen duality, and correspondingly weaker than the source: Proposition 4.4's `R̃(T) ≤ r + s^{ω/3}` needs that duality theorem, which this repository does not have |
| The free-lunch speedup: three mixed block families annihilating `S` give `S ⊵ T ⊕ T'`, as an explicit single-parameter degeneration of leading degree `2d+d'+2` | Alman–Li 2026 (arXiv:2605.21738), Theorem 5.1 and Corollary 5.1, pp. 14–15 | `polynomialDegeneratesAt_add_of_mixed_eq_zero`, `polynomialDegeneratesAt_directSum_of_blockPoly`, `polynomialDegeneratesAt_two_directSum_of_mixed_map_eq_zero` | `Tensor/FreeLunchSpeedup.lean` | any `CommSemiring`; the source's second degeneration parameter and its unbounded `ε = λ^k` are **dispensable** — the leading degree is computed instead — and the maximal-annihilator hypothesis is weakened to an arbitrary block family |
| The rank of a two-legged contraction, and the one-slice speedup `S ⊵ (f S) ⊕ ⟨1,t,1⟩` with `t = rank − dim X − dim Y` | Alman–Li 2026, Propositions 5.3 and 5.4, p. 17 | `matrixFlatten`, `matrixRank`, `map_ofLegs_eq_sum_pure_of_flatten`, `restricts_matrixMultiplication_of_matrixRank`, `polynomialDegenerates_directSum_oneSlice` | `Tensor/MatrixFlattening.lean`, `MatrixMultiplication/OneSlice{NormalForm,Speedup}.lean` | fields; the source's `T' ≅ ⟨1,t,1⟩` is stated as the restriction it actually is. Theorem 6.1 with a general slice size `s` is proved in its exact-rank form (`polynomialDegenerates_diagonalTensor_directSum_oneSlice`, `polynomialDegenerates_diagonalTensor_oneSlice_of_rankLE` in `MatrixMultiplication/NonminimalRankSpeedup.lean`), where the `s = n` clause needs no `s ≥ rank M` side condition; its border-rank form is the next row. Still recorded only as unproved `Prop`s: `OneSliceCompression` (Prop 5.7) and `DirectSumIdentity` (Thm 7.3) |
| **The one-slice speedup for a nonminimal *border*-rank decomposition: `R̲(T) ≤ r` for a tensor with `n`-dimensional `X` and `Y` legs gives `⟨r⟩ ⊕ ⟨1,n,1⟩ ⊵ T ⊕ ⟨1, r − n, 1⟩`**, and **the grouped speedup `⟨r⟩ ⊕ (p ⊙ ⟨1,n,1⟩) ⊵ T ⊕ (p ⊙ ⟨1,2n,1⟩)` whenever `3np ≤ r`** — both instances of one grouped core `⟨r⟩ ⊕ (p ⊙ ⟨1,n_Y,1⟩) ⊵ T ⊕ (p ⊙ ⟨1,m,1⟩)` for `p` groups of at least `m + n_X` certificate terms | Alman–Li 2026, Theorem 6.1, p. 19, and Theorem 6.3, pp. 21–22 | `polynomialDegenerates_diagonalTensor_oneSlice_of_borderRankLE`, `polynomialDegenerates_grouped_oneSlice_of_borderRankLE`, `AlmanLi.nonminimalBorderRankSpeedup`, `AlmanLi.groupedOneSliceSpeedup`, `Tensor.polynomialDegenerates_oneSliceFrameTensor_directSum_of_span`, `Tensor.exists_polynomial_kernel_frame` | `MatrixMultiplication/NonminimalBorderRankSpeedup.lean`, `MatrixMultiplication/GroupedBorderRankSpeedup.lean`, `Tensor/OneSliceBorderSpeedup.lean`, `Tensor/PolynomialKernelFrame.lean`, `Tensor/PolynomialScalar.lean` | fields, unconditional: the binders are the two leg dimensions and the `BorderRankLE r T` certificate, and the leg dimensions may differ (`⟨1,n_Y,1⟩` on the source, `r − n_X` on the target). **No function-field layer**: the source runs Propositions 5.3/5.4 over `F(λ)`; here two explicit polynomial families of leg maps are fed to the polynomial free-lunch theorem, and the dimension count is a kernel frame `P·δ = 0`, `αᵀ·δ = q·1` of the certificate's coordinate matrix over `K[X]`, found over the fraction field and returned with denominators cleared. Discharges the former named obligations `AlmanLi.NonminimalBorderRankSpeedup` and `AlmanLi.GroupedOneSliceSpeedup`. Theorem 6.3 is **not** obtained by applying Theorem 6.1 group by group, which is unavailable for a border certificate (one group's terms sum to a polynomial tensor with no leading term of its own); the core is grouped from the start. Its statement keeps the source's `finrank = n` hypotheses without finite-dimensionality, and the `n = 0` case is handled separately. Asserted in `AxiomAudit/OneSliceBorderSpeedup.lean` |
| The Galactic method: `ω ≤ ω_g`, `2 ≤ ω_g`, and `ω_g ≤ ω_g^coord` | AVW 2018, Definition 4.1 / Lemma 4.1 | `omega_le_galacticExponent`, `two_le_galacticExponent`, `galacticExponent_le_coordinateGalacticExponent` | `MatrixMultiplication/GalacticMethod.lean`, `IndependenceBarrier.lean` | fields; every inequality assumes that at least one certificate exists (`(galacticValues K T).Nonempty`, resp. `(coordinateGalacticValues K T).Nonempty` — `sInf ∅ = 0` in `ℝ`), and the comparison is stated for coefficient tables. `ω_g` is measured here by `R̲(T^{⊗n})` where AVW write `R̃(T)^n`; the AVW-shaped `galacticAsymptoticExponent` is proved `≤ ω_g`, with no equality claimed. Lemma 4.1 taken in its **equal-dimension reading** (option (i) of `BARRIER_FRAMEWORK.md` §6 D) |
| The universal method: `ω ≤ ω_u`, `2 ≤ ω_u`, `ω_u ≤ ω_g^sq` | Alman's thesis 2019 / Alman CCC 2019, §4.5 | `omega_le_universalExponent`, `two_le_universalExponent`, `universalExponent_le_squareGalacticExponent` | `MatrixMultiplication/UniversalMethod.lean` | fields; every inequality assumes that at least one certificate exists (`(universalValues K T).Nonempty`, resp. `(squareGalacticValues K T).Nonempty`). `ω_u` ranges over all polynomial degenerations and is measured by `R̃(T^{⊗n})`, where the thesis writes `r^n` for `R̃(T) ≤ r`; the thesis-shaped bound is `universalExponent_le_of_copies_of_asymptoticRank_le` |
| The value of a tensor `V_τ`, its calculus, and the value-to-exponent theorem: `R̃(T) ≤ r` and a certificate of `T` worth more than `r` at `τ` imply `ω < 3τ` | Coppersmith–Winograd 1990, §8 p. 264 | `tauValue`, `TauValueCertificate.term_le_asymptoticRank`, `omega_lt_three_mul_of_certificate`, `omega_lt_three_mul_of_approximate_certificates` | `MatrixMultiplication/TauValue{Core,Soundness}.lean` (umbrella `TauValue.lean`) | fields; the hypothesis is **strict** — the non-strict form is false at `⟨1,1,1⟩`. The supremum-level reading `r < V_τ(T)` is the separate `omega_lt_three_mul_of_lt_tauValue`, which also assumes `(tauValueValues F T τ).Nonempty`. The complete structural laws are recorded in the next row |
| The three CW90 value laws: `V_τ(A ⊞ B) ≥ V_τ(A)+V_τ(B)`, `V_τ(A ⊗ B) ≥ V_τ(A)·V_τ(B)`, `V_τ(T^{⊗k}) ≥ V_τ(T)^k` | Coppersmith–Winograd 1990, §8 p. 264 | `tauValue_add_le_tauValue_directSum`, `mul_tauValue_le_tauValue_external`, `tauValue_pow_le_tauValue_power`, `Isomorphic.externalPrefix_power_directSum_succ` | `MatrixMultiplication/TauValue{DirectSum,Superadditivity}.lean`, `Tensor/DirectSumPower.lean` | any `CommSemiring`; each supremum-level law carries its own `BddAbove` hypothesis (boundedness is known only for `τ ≤ ω/3`), nonemptiness of the input value sets (`sSup ∅ = 0`), and `k ≥ 1` for the power law. No Stirling estimate is needed |
| Bini's interpolation principle for the square exponent: `ω ≤ log r / log q` from a *border*-rank-`r` algorithm for `⟨q,q,q⟩`, in a degree-aware and a certificate-facing form | Bini–Capovani–Romani–Lotti 1979 / Bini 1980 | `omega_le_log_of_borderRankLEAt`, `omega_le_log_of_borderRankLE` | `MatrixMultiplication/BiniInterpolation.lean` | any `CommSemiring`; the only binders are `1 < q`, `1 ≤ r` and the certificate itself (`BorderRankLEAt r d ⟨q,q,q⟩`, resp. `BorderRankLE r ⟨q,q,q⟩`). The border-rank analogue of `omega_le_log_of_rankLE` above, and what the partial τ-theorem consumes. Asserted in `AxiomAudit/BiniInterpolation.lean` |
| Laser-volume regularization: one repetition of a `SubexponentialLaserVolumeSequence` *is* a CW90 value certificate, so the sequence certifies `laserVolumeValue stride copyBase volumeBase τ = (copyBase·volumeBase^τ)^(1/stride)` from below at every `τ ≥ 0`; hence `laserVolumeValue … (ω/3) ≤ R̃(T)`, `laserVolumeValue … τ ≤ V_τ(T)`, and the endpoint idiom in one step — `ω < 3τ`, or `ω < target` in base-two retained/mean-volume coordinates | this repository, over Coppersmith–Winograd 1990 §8 | `SubexponentialLaserVolumeSequence.exists_tauValueCertificate_term_ge`, `.le_tauValue_of_bddAbove`, `.le_tauValue`, `.laserVolumeValue_le_asymptoticRank`, `.omega_lt_three_mul_of_asymptoticRank_le`, `.omega_lt_three_mul_of_borderRankLE`, `.omega_lt_of_borderRankLE_bits` | `MatrixMultiplication/LaserVolumeRegularization.lean` | the regularization theorem and `le_tauValue_of_bddAbove` hold over any `CommSemiring`; the other five need a field. **Every one of them carries the structure-typed datum `h : SubexponentialLaserVolumeSequence F T stride copyBase volumeBase` as a binder**, so these are interface theorems, not bounds: they yield an `ω` bound only for a client that exhibits such a datum. Further binders: `0 ≤ τ` and `0 < ε` for the regularization theorem, `τ ≤ ω/3` for `le_tauValue`, `R̃(T) ≤ ρ` (resp. `BorderRankLE b T`) with the strict comparison against `laserVolumeValue` for the two `ω < 3τ` forms, and `0 ≤ target` with `b < 2^(retained + target·volume)` for the bit form |
| Direct-sum cyclic laser extraction rate of the exceptional CW `(1,1,2)` C-tensor, `(log(side²/Z) + (ω/3)·log volumeBase)/(3·stride)`, and its μ-entropy restatement `log 2·(2 − H₂(μ,μ,1−2μ) + ω(2−2μ)·log₂ q)/3` with `μ = L/(2(L+G))` | Coppersmith–Winograd 1990 §8, pp. 270–272 | `cw112_hasCyclicLaserExtractionRate`, `cw112_hasCyclicLaserExtractionRate_muEntropy` | `Examples/CoppersmithWinograd112CyclicValue.lean`, `…112CyclicValueFormula.lean` | any `CommRing`, unconditional; the only binders are `0 < q`, `0 < L`, `0 < G`. Deliberately the *flattened* shared-`Z` rate (copy base `side²/Z`), which is why the entropy term enters with a minus sign: the paper's optimized `112` value needs a superadditive C-tensor-family aggregation, and that is **not** claimed here |
| The repeated-orientation theorem: a labelled product of one-region degenerations degenerates factorwise under *any* orientation assignment, repetitions included, and the all-`(X,Z,Y)` six-region instance follows from the published six-*distinct*-slot theorem by one-hot time sharing | this repository | `DegenerationSystem.arbitrary_orientations`, `.six_repeated_xzy`, `.six_repeated_xzy_of_published_weights`, `.constituent_six_repeated_xzy_of_published_termWeights` | `MatrixMultiplication/RepeatedOrientation.lean` *(repository root)* | unconditional over the abstract `DegenerationSystem` class — no tensor model, no ring, no field. The binders are the orientation assignment, the factor family and the one-region degenerations themselves (for the published-weights forms, a family of standard-slot degenerations and the point-mass identification); **no theorem in the file has an injectivity or distinctness hypothesis**. `six_repeated_xzy` is asserted in `AxiomAudit/RepeatedOrientation.lean`, the other three in `AxiomAudit.lean` |
| The outer X-word ceiling (a *negative* result): every total-weight outer coarse cleanup retains **at most one** survivor — at every level, every recursion depth, every `q`, and for every choice of the three compatibility relations — so the `C′` outer-count record `OuterCountInput` is uninhabited at every depth | this repository, Total-Weight programme | `CWTotalWeightOuterCoarseCleanup.card_survivors_le_one`, `TotalWeightAcceptanceAssembly.false_of_outerCountInput`, `.isEmpty_outerCountInput`, `.isEmpty_levelTwoOuterCountInput`, `.isEmpty_levelFourOuterCountInput` | `MatrixMultiplication/TotalWeightOuterCeiling.lean` *(repository root)* | any `CommRing`; `card_survivors_le_one` is universally quantified over every cleanup datum and needs nothing further. The `IsEmpty` forms additionally bind `0 < stride`, the chunk alignment `∀ r, 0 < r → e·(stride·r) = 2^depth·(n r + 1)`, an `OuterFloorInput` and a coarse reference word; the depth-1 and depth-4 forms fix `q = 5`, `e = 8`, `stride = 38`. Audited only by the opt-in `AxiomAuditCertificate/TotalWeightOuterCeiling.lean`. Scope, per the module: it refutes the record's isolate-against-unrestricted shape, not the hash-first flat frame |
| Classical CW tensor-square regression `ω < 2.38` | Coppersmith–Winograd 1990, Sections 6–8 | `coppersmithWinograd_square_omega_lt_238` | `Examples/CoppersmithWinograd238.lean`, `CoppersmithWinograd238Arithmetic.lean` | any field; unconditional finite degeneration/value certificates and exact rational atanh arithmetic; sharpened to `2.375477` in the next row |
| **`ω < 2.375477`** — the optimized classical CW tensor square, at the exact integral profile `q = 6`, `τ = 2375477/3000000`, `(A,B,C,D) = (148446, 7976570, 65404408, 131096512)`, `(L,G) = (7,247)` | Coppersmith–Winograd 1990 §§7–8, pp. 267–272 | `coppersmithWinograd_square_omega_lt_2375477`, `cwSquare2375477_stable_value_gt_64` | `Examples/CoppersmithWinograd2375477.lean`, `CoppersmithWinograd2375477Arithmetic.lean` | any field, **unconditional**: the only binders are `K` and `[Field K]`. Exact-rational directed-logarithm certificate, no floating point — the strict value comparison `64 < cwSquareSymmetric112LimitLowerTerm …` is proved, not assumed, and every hypothesis of the parametric endpoint `cwSquareSymmetric112_omega_lt_three_mul` is discharged at that profile. Cited by `Frontier.lean` as the classical record |
| **`ω < 2.374631`** — Duan–Wu–Zhou's second-power (level-two) bound on `CW_6^{⊗2}`, proved as the paper argues it: hashing to the marked reference family, Additional Zeroing-Out Steps 1–2 on the cut ambient, the hole lemma and seeded batching, with the explicit period family `dwz63PeriodSeq` discharging every side condition | Duan–Wu–Zhou 2022 (arXiv 2210.10173) §6.3, `global_value.tex:332-378`, stated bound at `:352`; certificate = the published level-two parameters | `omega_lt_2374631`, `omega_lt_2374631_of_seededPeriod_applied` | `Examples/DuanWuZhouLevelTwoOmegaBound.lean` (umbrella `AlgebraicComplexity/DuanWuZhouLevelTwo.lean`; audit `AxiomAudit/DuanWuZhouLevelTwoOmegaBound.lean`) | any `Field`, **unconditional**; the strongest unconditional exponent bound in the tree. Not the paper's headline `2.371866`, which comes from higher powers and is not claimed |

### Lower bounds on rank and border rank

Everything in this table is unconditional over an arbitrary field.

| Result | Source | Lean declaration | Module | Hypotheses / status |
| --- | --- | --- | --- | --- |
| `rank ⟨2,2,2⟩ = 7` (with `7 ≤ rank` the substantive half) | Winograd 1971; Hopcroft–Kerr 1971 Theorem 3 (mod 2) | `rank_matrixMultiplication_two`, `seven_le_rank_matrixMultiplication_two`, `Winograd.Computes.length_ge_seven` | `Examples/WinogradLowerBound.lean` | **any field** — stronger than Hopcroft–Kerr's mod-2 statement; proof follows Bläser–Christandl–Zuiddam |
| Substitution stepping stones `n·p + 1`, `n·p + 2`, hence `rank ⟨2,2,2⟩ ≥ 5, ≥ 6` | substitution method (Hopcroft–Kerr / Winograd lineage) | `matrixMultiplication_rank_lower_substitution_Y`, `matrixMultiplication_rank_lower_double_substitution_Y`, `five_le_rank_matrixMultiplication_two`, `six_le_rank_matrixMultiplication_two` | `Tensor/SubstitutionMethod.lean`, `Examples/SmallMatrixLowerBounds.lean`, `Examples/BlaeserLowerBound.lean` | any field; `2 ≤ m` and positive `n, p` for `n·p + 1`, `2 ≤ m`, `2 ≤ n` and positive `p` for `n·p + 2` |
| Row-kill bound `(m−1)·n + n·p ≤ rank ⟨m,n,p⟩` | Bläser-direction substitution argument | `rank_matrixMultiplication_rowKill` | `Examples/BlaeserLowerBound.lean` | any field, all positive `m, p` |
| `2n² − n ≤ rank ⟨n,n,n⟩` | Bläser-direction; the apparent ceiling of the uniform-substitution fragment (informal, recorded in the module doc) | `two_sq_sub_le_rank_matrixMultiplication_square` | `Examples/BlaeserLowerBound.lean` | any field, positive `n`; Bläser's `5/2·n²` is **not** proved (named obstruction recorded in the module) |
| Koszul flattenings, and `6 ≤ rank ⟨2,2,2⟩` independently of substitution | Landsberg–Ottaviani | `Tensor.lt_rank_of_linearIndependent_koszulFlattening`, `six_le_rank_matrixMultiplication_two_koszul` | `Tensor/KoszulFlattening.lean`, `MatrixMultiplication/KoszulBorderRank.lean` | any field; the *border*-rank half is blocked on `K[ε]` exterior-power base change and is not claimed |
| Border-rank conciseness: a concise degeneration has border rank at least the largest leg dimension | notes Theorem 3.4 | `Tensor.max_finrank_le_borderRank`, `max_le_borderRank_matrixMultiplication` | `Tensor/BorderConcise.lean`, `MatrixMultiplication/BorderConcise.lean` | any field; positive `m, n, p` for the matrix-multiplication corollary; determinant-free leading-coefficient span argument |
| `q + 2 ≤ R̃(CW_q^σ)` for every `q` and every `σ`, because `CW_q^σ` is coordinate-concise on all three legs; together with `R̲(CW_q^id) ≤ q + 2` above this pins `R̃(CW_q) = q + 2` at `σ = id` | AVW 2018, Lemma 7.2, step 3 | `card_le_asymptoticRank_gcwTable`, `isCoordinateConcise_gcwTable` | `Examples/GeneralizedCoppersmithWinogradBarrier.lean` | any field, unconditional; `μ` finite with decidable equality and `σ` arbitrary, no further binder. No equality declaration exists in the tree — `R̃(CW_q) = q + 2` is the two halves put together by the reader |
| Slice rank of the diagonal: `sliceRank(diag n) = n` | Tao 2016 (Tao–Sawin) | `Tensor.sliceRank_diagonalTensor`, `Tensor.rank_diagonalTensor` | `Tensor/SliceRank.lean` | any field |
| A size-`m` diagonal restriction forces `m ≤ sliceRank T` — the finite core of the universal-method `S̃` barrier and of the chain `I ≤ subrank ≤ sliceRank` | Tao–Sawin 2016 | `Tensor.card_le_sliceRank_of_restricts_diagonalTensor` | `Tensor/SliceRank.lean` | any field |
| The chain `subrank ≤ sliceRank ≤ rank`, and asymptotic subrank via the Fekete engine | Strassen; Tao | `Tensor.subrank_le_sliceRank`, `Tensor.sliceRank_le_rank`, `Tensor.tendsto_asymptoticSubrank` | `Tensor/Subrank.lean`, `Tensor/SliceRank.lean`, `Tensor/AsymptoticInvariant.lean` | multiplicative Fekete lemma proved in `Asymptotics.lean`; the convergence statement assumes that `T` restricts onto `⟨1⟩`, i.e. has nonzero subrank |
| `I(T) ≤ subrank(T)`, and `I` is genuinely basis-dependent | AVW 2018 §1 | `Tensor.independenceNumber_le_subrank`, `Tensor.HadamardWitness.independenceNumber_not_isomorphism_invariant` | `Tensor/IndependenceNumber.lean` | the witness is the `ℚ` Hadamard change of basis on `⟨2⟩` |
| Strassen's commutation equations: at minimal border rank `R̲(T) ≤ n` with one invertible `Z`-slice, the normalized slices `Q·M_z` pairwise commute — hence a non-commuting pair certifies `R̲(T) > n` | Strassen 1983 | `Tensor.normalizedSlices_commute_of_borderRankLE`, `Tensor.not_borderRankLE_of_normalizedSlices_ne`, `Tensor.lt_borderRank_of_normalizedSlices_ne` | `Tensor/StrassenEquations.lean` | any `CommRing`; adjugate/determinant argument, no field or genericity assumption |
| The row-kill bound taken over all three legs (`⟨3,3,3⟩ ≥ 15` and `⟨2,2,2⟩ ≥ 6` fall out as unnamed regression `example`s) | Bläser-direction | `matrixMultiplication_rank_lower_rowKill_max`, `matrixMultiplication_square_rank_lower` | `Examples/BlaeserLowerBound.lean` | any field, all positive `m, n, p` (resp. `n`); stated on rank certificates `RankLE r` |

### Barriers: the Alman–Vassilevska Williams program (arXiv:1810.08671)

`BARRIER_FRAMEWORK.md` is the contract for this table; §6 carries the per-milestone status notes
and §7 the acceptance criteria.

| Result | Source | Lean declaration | Module | Hypotheses / status |
| --- | --- | --- | --- | --- |
| Powers of `I`, supermultiplicativity, and `Ī(T)` as a Fekete limit with `Ī(T^{⊗k}) = Ī(T)^k` for `k ≥ 1` | AVW Section 4 (milestones A, B) | `Tensor.independenceNumber_coordinatePower_add_ge`, `Tensor.asymptoticIndependenceNumber`, `Tensor.asymptoticIndependenceNumber_coordinatePower` | `Tensor/IndependenceNumber.lean`, `Tensor/AsymptoticIndependenceNumber.lean` | any `CommSemiring` with `NoZeroDivisors`, `Nontrivial` |
| Monomial degenerations feed `Ī`: Lemma 4.3 with explicit polynomial loss, Corollaries 4.1–4.2 | AVW Lemma 4.3, Cor. 4.1–4.2 | `Tensor.MonomialIndependence.monomialDegenerates_coordinateTensor_minimumWeightPart`, `Tensor.pow_card_le_mul_independenceNumber_coordinatePower`, `Tensor.card_le_asymptoticIndependenceNumber`, `Tensor.asymptoticIndependenceNumber_minimumWeightPart_le` | `Tensor/MonomialIndependence.lean` | `CommSemiring` + `NoZeroDivisors` + `Nontrivial` (the degeneration bridge alone needs only `CommSemiring`), with the minimum-weight side condition; stated on the **degenerated** table `D`, per the Lemma 4.2 correction |
| Lemma 4.2 (Strassen weights) — finite half, with the unweakened `3/4` constant for all dimensions | AVW Lemma 4.2 | `independentSet_mmMinWeightSupport`, `exists_three_mul_le_independenceNumber_mmMinWeight` | `MatrixMultiplication/IndependentDiagonal.lean` | `CommSemiring` + `Nontrivial`; no parity hypothesis; **correction**: the min-weight triples are *not in general* independent in `⟨a,b,c⟩`'s own table — the formal counterexample is `⟨3,3,3⟩` at level 3 (`not_independentSet_mmCoefficients_mmMinWeightSupport`) |
| Lemma 4.4: `Ī⟨m,n,p⟩ = mnp / max{m,n,p}`, exactly, for all dimensions; plus the `F`-copies form | AVW Lemma 4.4 | `asymptoticIndependenceNumber_mmCoefficients`, `asymptoticIndependenceNumber_mmCoefficients_copies` | `MatrixMultiplication/IndependentDiagonal.lean` | `CommSemiring` + `NoZeroDivisors` + `Nontrivial`; an equality, not just a bound |
| **Theorem 4.1 / Corollary 4.3**: `Ī(T) ≥ R̃(T)^{6/ω_g(T) − 2}`, in the explicit `w = 6/(s+2)` form | AVW Theorem 4.1, Cor. 4.3 | `rpow_coordinateGalacticExponent_le_asymptoticIndependenceNumber_of_concise`, `six_div_add_two_le_coordinateGalacticExponent`, `two_lt_coordinateGalacticExponent_of_concise` | `MatrixMultiplication/IndependenceBarrier.lean` | fields, for the **coordinate** Galactic exponent (see the errata section); each statement assumes that a coordinate certificate exists (`(coordinateGalacticValues K T).Nonempty` — the exponent is an `sInf`), the `_of_concise` forms take coordinate conciseness, and `six_div_add_two_le_coordinateGalacticExponent` is the abstract-`R` form, the displayed `R̃(T)` reading being `six_div_add_two_le_coordinateGalacticExponent_of_concise` |
| Definition 5.2, Claim 5.1, **Theorem 5.3**: `Ī(T) ≤ Σ μ(P_i)^{1/3}` | AVW Def. 5.2, Claim 5.1, Thm 5.3 | `Tensor.independenceNumber_pow_three_le_coordinateMeasure`, `Tensor.asymptoticIndependenceNumber_le_sum_rpow_coordinateMeasure_of_cover` | `Tensor/IndependenceMeasure.lean` | **stronger than printed**: covers not just partitions, plain `CommSemiring`, and *no* polynomial loss |
| Lemma 5.1, the binomial tail, by the method of types (no measure theory) | AVW Lemma 5.1 | `BinomialTail.card_deviatingWords_le`, `BinomialTail.card_deviatingWords_le_rpow_sqrt`, `BinomialTail.exponentialRate_deviatingWords_le` | `Combinatorics/BinomialTail.lean` | `tailExponent ε = 2ε²`, AVW's sharp constant, via binary Pinsker; the finite-`n` bounds carry a polynomial `(n+1)` factor that AVW's Hoeffding route does not, removed again in `exponentialRate_deviatingWords_le` |
| Binary and finite-alphabet Pinsker inequalities (what makes Lemma 5.1 sharp) | classical | `ProbabilityVector.two_mul_sq_sub_le_binaryKlDiv`, `ProbabilityVector.sq_sum_abs_sub_le_two_mul_klDiv` | `Probability/KullbackLeiblerBounds.lean` | unconditional |
| **Theorem 5.1**, the splitting bound, plus Remark 5.1 and both AVW numerical certificates (`≤ 5.08`, `< 8`) | AVW Def. 5.1, Thm 5.1, Rem. 5.1 | `Tensor.asymptoticIndependenceNumber_le_splittingBound`, `Tensor.splittingBound_le`, `Tensor.splittingBound_lt`, `Tensor.asymptoticIndependenceNumber_le_of_splitVariable_seven`, `Tensor.asymptoticIndependenceNumber_lt_eight_of_splitVariable` | `Tensor/IndependenceSplitting.lean` | needs `NoZeroDivisors` + `Nontrivial`; pure rational arithmetic, no floating point. Remark 5.1 is `splittingBound ≤ Q`, strict when `p·Q ≠ 1`; the `c`-form of AVW's extremal case is not formalized. `Tensor.splittingBound_le` carries no `#assert_axioms` line |
| **Theorem 5.2 / Corollary 5.1**: a corner configuration — every `x_q`-term and every `y_q`-term passes through one `z₁`, and no term uses both — forces `Ī(T) < q`, with `cornerExponent q = 1/(q²(q+1)² log q)` | AVW Thm 5.2, Cor. 5.1 | `Tensor.exists_probabilityVector_uniformWindow_le_supportMarginal`, `asymptoticIndependenceNumber_le_cornerBound`, `cornerBound_lt` | `MatrixMultiplication/IndependenceMassDistribution.lean` | needs `NoZeroDivisors`; **correction**: the *existence* of AVW's second corner term `x₁y_qz₁` is unused (`_hyterm` in `asymptoticIndependenceNumber_le_cornerBound_of_corner_terms`) |
| Lemma 6.1 as an **equality**: `I(T_G) = triColoredSumFreeNumber G` | AVW Lemma 6.1 | `Examples.independenceNumber_groupCoefficients` | `Examples/GroupTensorBarrier.lean` | both directions; any finite group |
| **Theorem 6.1**: `ω_g^coord(T_G) > 2` for every finite group | AVW Theorem 6.1 (via Sawin's Theorem 3.2) | `Examples.two_lt_coordinateGalacticExponent_groupCoefficients_of_sawinBound` | `Examples/GroupTensorBarrier.lean` | **conditional on the named proof obligation `SawinBound G`** |
| **Theorem 7.1**: a universal `c > 2` with `ω_g^coord(CW_q^σ) ≥ c` for *every* generalized CW tensor and every `σ` | AVW Theorem 7.1 (Lemmas 7.1, 7.2) | `avw_theorem_seven_one`, `avw_theorem_seven_one_exists`, `avwTheoremSevenOneConstant`, `two_add_le_avwTheoremSevenOneConstant` | `Examples/GeneralizedCoppersmithWinogradBarrier.lean` | any field; explicit constant `min (60000/29999) (6/(3 − cornerExponent 7))`, certified `≥ 2 + 1/15000` by exact rational atanh enclosures |
| **Theorem 7.1, sharpened**: the same universal barrier with the constant raised to `min (600/293) (6/(3 − cornerExponent 2)) = 2.027078…`, certified `≥ 2 + 27/1000` | this repository, Theorem 7.1 fed by Alman's block-entropy bound | `avwTheoremSevenOneSharpConstant`, `avwTheoremSevenOneSharpConstant_eq`, `two_add_le_avwTheoremSevenOneSharpConstant`, `avw_theorem_seven_one_sharp_unconditional`, `avw_theorem_seven_one_exists_sharp_unconditional` | `Examples/GeneralizedCoppersmithWinogradBarrier.lean`, `Examples/GeneralizedCoppersmithWinogradSharpBarrier.lean` | any field, **unconditional**; three orders of magnitude above the `2 + 1/15000` that AVW's Lemma 7.2 splitting argument forces. The entropy input is an explicit hypothesis upstream (import order) and is discharged in the `SharpBarrier` module |
| **Theorem 7.2**: the tensor of every finite group of order `≥ 2` monomially degenerates to a generalized CW tensor of parameter `card G − 2` | AVW Theorem 7.2 | `groupTensorMul_monomialDegenerates_isGeneralizedCW` (abstract); `groupTensor_monomialDegenerates_isGeneralizedCW`, `minimumWeightPart_avwSymWeight` (coefficient table) | `Examples/GeneralizedCoppersmithWinograd.lean`, `Examples/GroupTensorCWDegeneration.lean` | any `CommSemiring`; the explicit forms fix a witness `g ≠ 1`, so they say nothing about the trivial group (the `[Nontrivial G]` existential forms are `exists_monomialDegenerates_isGeneralizedCW` and `exists_groupTensor_monomialDegenerates_isGeneralizedCW`). The table form is what the `Ī` bridge `asymptoticIndependenceNumber_gcwTable_le_groupCoefficients` needs, and that bridge also takes `NoZeroDivisors` + `Nontrivial` on `K` |
| **Theorem 7.3**: `(q+2)^{2/f(q)} ≤ Ī(CW_q^σ)`, and the cube form `(27/4)q² ≤ Ī(CW_q^σ)³` | AVW Theorem 7.3 (from CW90 §6) | `avw_theorem_seven_three`, `easyCW_independence_base_inequality`, `avwF` | `Examples/GeneralizedCoppersmithWinogradIndependenceLower.lean`, `Examples/CoppersmithWinogradEasyCoordinate.lean` | `CommSemiring` + `NoZeroDivisors` + `Nontrivial`; `q ≥ 2` for the `f(q)` form and `q ≥ 1` for the cube form; **cube form is stronger than the paper**; erratum: `f(1)` is undefined |
| Remark 7.2, strengthened from `q ≥ 3` to `q ≥ 2`; and the sandwich `(q+2)^{2/f(q)} ≤ Ī(CW_q^σ) ≤ cornerBound(q+2) < q+2` | AVW Remark 7.2 | `avw_remark_seven_two`, `avw_gcwTable_independence_sandwich` | `Examples/GeneralizedCoppersmithWinogradIndependenceLower.lean` | same hypotheses; the upper half needs no hypothesis on `q` |
| **Theorem 7.4**: `card G ^ (2/f(card G − 2)) ≤ Ī(T_G)`, plus the tri-colored sum-free consequence and a bound on any Sawin constant | AVW Theorem 7.4 | `avw_theorem_seven_four`, `avw_theorem_seven_four_exists_of_four_le`, `avw_theorem_seven_four_triColoredSumFree`, `le_sawinConstant`, `avwGroupExponent` | `Examples/GroupTensorIndependenceLower.lean` | `CommSemiring` + `NoZeroDivisors` + `Nontrivial`. The displayed exponent `2/f(card G − 2)` needs `card G ≥ 4` (`avw_theorem_seven_four`), and strictness `c > 2/3` needs `≥ 5`; **existence of some `c > 2/3` is proved for every finite group with `card G ≥ 2`** (AVW need `≥ 5`) via `avw_theorem_seven_four_exists_of_two_le`, whose witness is `avwCubeExponent (card G²)` and which lifts the cube bound to `T_G^{⊗n}` before extracting the exponent. `le_sawinConstant` needs `card G ≥ 3` and takes the tri-coloured sum-free bound for `δ` as a hypothesis |
| Theorem 7.4 at the small orders, as certified rationals: `Ī(T_{C₂}) ≥ 1.84`, `Ī(T_G) ≥ 2.629` at order 3, `Ī(T_G) ≥ 3.31` at order 4 | this repository, from the power lift | `rat_le_asymptoticIndependenceNumber_groupCoefficients_of_card_eq_two`, `…_of_card_eq_three`, `…_of_card_eq_four`, and the `rpow_…` exact forms | `Examples/GroupTensorIndependenceLower.lean` | any `CommSemiring` + `NoZeroDivisors` + `Nontrivial`; the Kleinberg–Sawin–Speyer values (e.g. `2.75510…` at order 3) are **not** claimed |
| Constraints on any Sawin constant at small orders: `δ ≥ 0.92` (order 2), `δ ≥ 0.876` (order 3), `δ ≥ 0.828` (order 4) | this repository, dual reading of Theorem 7.4 | `rat_le_sawinConstant_of_card_eq_two`, `rat_le_sawinConstant_of_card_eq_three`, `rat_le_sawinConstant_of_card_eq_four`, `three_div_four_le_sawinConstant_of_card_eq_four` | `Examples/GroupTensorIndependenceLower.lean` | takes the tri-colored sum-free bound for `δ` as a hypothesis; at order 2 this is the *first* constraint available, since `le_sawinConstant` is empty there |
| **Theorem 7.5**: the Galactic barrier for lower-triangular tensors, with an explicit constant | AVW Theorem 7.5 | `avw_theorem_seven_five`, `two_lt_coordinateGalacticExponent_lowerTriangularTable` | `Examples/LowerTriangularBarrier.lean` | any field, `q ≥ 2`; explicit constant `6/(3 − cornerExponent q)` — AVW leave `c_q` unnamed |
| **Theorem 7.6**: for lower-triangular `T`, `Ī(T) = q ↔ T` has an independent diagonal; quantitatively `Ī ≤ q^{1 − diagonalExponent q}` otherwise | AVW Theorem 7.6 | `avw_theorem_seven_six`, `diagonalExponent`, `asymptoticIndependenceNumber_le_diagonalBound_of_not_hasIndependentDiagonal`, `six_div_sub_diagonalExponent_le_coordinateGalacticExponent` | `Examples/LowerTriangularDiagonal.lean`, `MatrixMultiplication/IndependenceMassDistribution.lean` (`diagonalExponent`) | `q ≥ 2` and `CommSemiring` + `NoZeroDivisors` + `Nontrivial` — no field needed for the equivalence or the quantitative bound, while the Galactic corollary `six_div_sub_diagonalExponent_le_coordinateGalacticExponent` is over a field and additionally takes coordinate conciseness, `q ≤ R̃(T)` and a nonempty certificate set; explicit `diagonalExponent q = 1/((q(1 + q2^q − q²))² log q)`, replacing AVW's `O_q(κ)` bookkeeping |
| **Milestone M8**: `ω_g^coord(CW_q^σ) ≤ f(q)`, and the two-sided sandwich `2 + 1/15000 ≤ ω_g^coord(CW_q) ≤ f(q)` | AVW Section 7 by-product | `coordinateGalacticExponent_gcwTable_le_avwF`, `coordinateGalacticExponent_gcwTable_refl_le_avwF`, `avw_galactic_exponent_gcwTable_sandwich`, `avw_galactic_exponent_gcwTable_fin_six` | `Examples/GeneralizedCoppersmithWinogradGalacticUpper.lean` | any field, `q ≥ 2` (the `q = 6` instance needs no further hypothesis); the general-`σ` form takes `R̲(genCW K μ σ) ≤ q+2` as an explicit hypothesis, discharged for `σ = id`; numeric instance `2 + 1/15000 ≤ ω_g^coord(CW_6) ≤ 2.416` |
| The border-rank dichotomy for a twisted CW tensor: the normalized slices of `CW_q^σ` commute iff `σ` is an involution, so `R̲(CW_q^σ) ≥ q + 3` whenever `σ(σ i) ≠ i` for some `i` | this repository, via Strassen's equations | `genCW_normalizedSlices_commute_of_involutive`, `not_borderRankLE_genCW_of_not_involutive`, `borderRank_genCW_ge_of_not_involutive`, `not_borderRankLE_genCW_threeCycle` | `Examples/GeneralizedCoppersmithWinogradStrassen.lean` | any `Nontrivial CommRing`; the smallest witness is the three-cycle at `q = 3` over `ℚ`. This is the *negative* half of the M8 hypothesis: for a non-involutive `σ` the minimal border rank `q+2` of `genCW_borderRankLE_refl` is unavailable |
| Remark 7.3: `6.419 ≤ Ī(CW_6^σ)` from the first-power coordinate certificate | AVW Remark 7.3 | `avw_remark_seven_three` | `Examples/CoppersmithWinogradFirstPowerCoordinate.lean`, `MatrixMultiplication/CoordinateBlockCertificate.lean` | AVW's Remark 7.3 prints no numeric value: the `6.4194…` figure is this repository's own projection from the exact optimizer (`LOWER_BOUNDS_ROADMAP.md`), and the certified rational type gives `6.419` (exact limit `6.41933…`) |
| Lemmas 6.2/6.3: `CW_q` is not a sub-tensor of `T_G` for abelian `card G < 2q` | AVW Lemmas 6.2, 6.3 | `not_isSubTensor_coppersmithWinograd_groupTensor` | `Examples/CoppersmithWinogradGroupExclusion.lean` | stated with **weaker hypotheses than the paper** |

### Barriers: the universal method (Alman's thesis 2019 / CCC 2019)

| Result | Source | Lean declaration | Module | Hypotheses / status |
| --- | --- | --- | --- | --- |
| The universal exponent `ω_u` (a single square target, all polynomial degenerations) | Alman 2019, §4.5 | `universalExponent`, `universalBorderExponent`, `universalExponent_le_of_certificate` | `MatrixMultiplication/UniversalMethod.lean` | fields |
| **Proposition 4.3**: one matrix-multiplication tensor without loss of generality | Alman 2019, Prop. 4.3 | `universalExponent_le_of_copies_of_asymptoticRank_le` | `MatrixMultiplication/UniversalMethod.lean` | fields; explicit `(n log r − log F)/log q` form |
| **Theorem 5.1 / Corollary 5.2**: `ω_u(T) ≥ 2 log R / log S`, and `ω_u(T) > 2` from a strict measure gap | Alman 2019, Thm 5.1, Cor. 5.2 | `two_mul_log_div_log_le_universalExponent_of_measure`, `two_mul_log_asymptoticRank_div_log_le_universalExponent`, `two_lt_universalExponent` | `MatrixMultiplication/UniversalMethod.lean` | abstract form, for a `T` with at least one universal certificate (`(universalValues K T).Nonempty`); the `R̃(T)` form also needs nonvanishing powers and `R̃(T) > 0`; the `2/s` constant is strictly stronger than AVW's `6/(s+2)` |
| **Theorem 5.1 / Corollary 5.2 instantiated at the asymptotic slice rank**: `ω_u(T) ≥ 2 log R̃(T) / log S̃(T)`, and `ω_u(T) > 2` from a strictly sublinear `S̃` | Alman 2019, §5.2 | `two_mul_log_asymptoticRank_div_log_asymptoticSliceRank_le_universalExponent`, `two_div_le_universalExponent_of_asymptoticSliceRank`, `two_lt_universalExponent_of_asymptoticSliceRank`, and the primed unconditional form `…_le_universalExponent'` | `MatrixMultiplication/UniversalSliceRankBarrier.lean` | **unconditional** over any field: the obligation hypothesis is discharged by `Tensor.sliceRankDegenerationMonotone_holds` |
| Slice rank along a single leg, and `asymptoticSliceRank` as a limsup with `S̃(diag n) = n` | Alman 2019, Ch. 5 | `Tensor.sliceRankAlong`, `asymptoticSliceRank`, `Tensor.asymptoticSliceRank_diagonalTensor` | `Tensor/SliceRank.lean`, `Tensor/AsymptoticSliceRank.lean` | with `S̃ ≤ R̃` and `Ī ≤ S̃` (`Tensor.asymptoticIndependenceNumber_le_asymptoticSliceRank`) |
| **Proposition 5.1 = Tao–Sawin Corollary 2, now proved**: polynomial degeneration never increases slice rank, with no leading-term hypothesis | Tao–Sawin 2016, Cor. 2 (Alman 2019, Prop. 5.1) | `Tensor.sliceRank_le_of_polynomialDegenerates`, `Tensor.sliceRankDegenerationMonotone_holds`, `Tensor.sliceRank_polynomialDegenerates_le`, `Tensor.sliceRank_le_of_hasLeadingTerm` | `Tensor/SliceRankSaturation.lean`, `Tensor/SliceRankDegeneration.lean` | any field; `Tensor.sliceRank_le_of_hasLeadingTerm` is the earlier first-order case and is still conditional on the leading-degree hypothesis `hfirst`, while the other three are unconditional, by saturating the polynomial transform (`exists_polynomialLinearMap_fixing_list`) rather than assuming a leading term. **This retires the former named obligation `SliceRankDegenerationMonotone`**, whose `Prop` survives only as the universe-explicit packaging |
| **Thesis Theorem 5.3** for `Ī`: the block-partition entropy bound, loss-free | Alman 2019, Thm 5.3 (§5.3.2) | `Tensor.asymptoticIndependenceNumber_le_of_blockEntropy`, `blockLegValue` | `Tensor/IndependenceBlockEntropy.lean`, `Probability/EntropyValue.lean` | `NoZeroDivisors` + `Nontrivial`; one term of the multinomial expansion, no `poly(n)` loss |
| **Thesis Theorem 5.3** for `S̃`: the same block-partition entropy bound for the asymptotic slice rank, plus the raw fiber-count form | Alman 2019, Thm 5.3 (§5.3.2) | `Tensor.asymptoticSliceRank_coordinateTensor_le_of_blockEntropy`, `Tensor.asymptoticSliceRank_coordinateTensor_le_sum_blockFiberCard`, `Tensor.asymptoticSliceRank_le_of_subexponential_mul_pow` | `Tensor/SliceRankBlockEntropy.lean` | any `CommSemiring`, with no zero-divisor hypothesis; the stronger of the pair, since `Ī ≤ S̃` — over a field the `Ī` bound above is recovered from it |
| `Ī(CW_q^σ) ≤ u^{1/3}(q + u + 1/u)`; certified `Ī(CW_6^σ) ≤ 6.45` and `Ī(CW_1^σ) ≤ 2.7552` | Alman 2019 (thesis value `6.44493`) | `asymptoticIndependenceNumber_gcwTable_le_rpow_mul`, `asymptoticIndependenceNumber_gcwTable_fin_six_le`, `asymptoticIndependenceNumber_gcwTable_fin_one_le` | `Examples/GeneralizedCoppersmithWinogradIndependenceUpper.lean` | any `CommSemiring` + `NoZeroDivisors` + `Nontrivial`; `q ≥ 1`, `u > 0`; the Legendre dual of Alman's `sup_v` formula |
| `S̃(CW_q^σ) ≤ u^{1/3}(q + u + 1/u)`; certified `S̃(CW_6^σ) ≤ 6.45` (`u = (13/20)³`) and `S̃(CW_1^σ) ≤ 2.7552` (`u = (21/25)³`) | Alman 2019, table p. 71 (`6.44493…`, `2.7551…`) | `asymptoticSliceRank_gcwTable_le_rpow_mul`, `asymptoticSliceRank_gcwTable_fin_six_le`, `asymptoticSliceRank_gcwTable_fin_one_le`, `asymptoticSliceRank_gcwTable_le_rpow_sharp` | `Examples/GeneralizedCoppersmithWinogradSliceRankUpper.lean`, `Examples/GeneralizedCoppersmithWinogradUniversalBarrier.lean` | nontrivial commutative semiring for the three block-entropy bounds and a field only for `asymptoticSliceRank_gcwTable_le_rpow_sharp`; `q ≥ 1`, `u > 0`; exact rational certificates, no floating point. `q = 1` is the binding instance for the universal barrier |
| The `q = 6` sandwich `6.24 ≤ Ī(CW_6^σ) ≤ 6.45`, sharpening the `< 8` of AVW's Theorem 5.1 (the second proof of Lemma 7.2) | this repository's cube inequality `(27/4)q² ≤ Ī³` below, strengthening AVW Theorem 7.3 / Remark 7.2; Alman 2019 §5.5.1 above | `avw_gcwTable_independence_sandwich_upper_fin_six` | `Examples/GeneralizedCoppersmithWinogradIndependenceUpper.lean` | commutative semiring with `NoZeroDivisors` + `Nontrivial` (no field needed); the lower half is sharpened to `6.419 ≤ Ī(CW_6^σ)` by `avw_remark_seven_three` (first-power coordinate certificate); the remaining gap `[6.4193, 6.4450]` can only be closed from below |
| The sharpened Galactic barrier `ω_g^coord(CW_6^σ) ≥ 29/14 = 2.0714…` | this repository, from the two results above | `coordinateGalacticExponent_gcwTable_fin_six_ge`, `two_lt_coordinateGalacticExponent_gcwTable_fin_six` | `Examples/GeneralizedCoppersmithWinogradIndependenceUpper.lean` | any field; replaces the `2.0000666…` that Theorem 7.1 gives at `q = 6` |
| **Thesis Theorem 5.7**: the universal-method barrier for every generalized CW tensor, `ω_u(CW_q^σ) ≥ 13/6 = 2.1666…`, hence `ω_u(CW_q^σ) > 2` | Alman 2019, Thm 5.7 | `thirteen_div_six_le_universalExponent_gcwTable`, `thirteen_div_six_le_universalExponent_gcwTable'`, `two_lt_universalExponent_gcwTable'` | `Examples/GeneralizedCoppersmithWinogradUniversalBarrier.lean` | any field, `q ≥ 1`; the primed forms are **unconditional**. `hne` (at least one universal certificate exists) is genuinely necessary — `universalExponent` is an `sInf` and Lean's `sInf ∅ = 0` |
| The same barrier sharpened to `ω_u(CW_q^σ) ≥ 2.168`, uniformly in `q` and `σ` | this repository, from the sharp block-entropy certificate | `avw_thesis_constant_le_universalExponent_gcwTable` | `Examples/GeneralizedCoppersmithWinogradUniversalBarrier.lean` | any field, `q ≥ 1`, unconditional; within `5.3·10⁻⁵` of the thesis constant, which is a `q = 1` statement |
| The thesis table entries themselves: `ω_u(CW_1^σ) ≥ 2.16805229` and `ω_u(CW_5^σ) ≥ 2.21912378` | Alman 2019, Thm 5.7 / table p. 71 (`2.1680525…`, `2.21912…`) | `thesis_constant_le_universalExponent_gcwTable_card_one`, `thesis_constant_le_universalExponent_gcwTable_card_five` | `Examples/GeneralizedCoppersmithWinogradUniversalBarrier.lean` | any field, unconditional (with the same `hne` as Theorem 5.7 above); eight certified digits — the margin at `2.16805229` is `2.1·10⁻⁹`, and the rational certificates are `S̃ ≤ 474609871/172265625` and `S̃ ≤ 127218805/22024249` |

### Named proof obligations (explicitly *not* proved)

Per the policy in `DESIGN.md`, an unproved deep input is a `Prop` definition exposed as an explicit
hypothesis of every theorem that consumes it. It is never introduced with `axiom`, never hidden in
a typeclass instance, and never reported as proved.

| Obligation | What it stands for | Lean declaration | Module | Who depends on it |
| --- | --- | --- | --- | --- |
| Sawin's theorem | tri-colored sum-free sets in `G^n` have size at most `(δ card G)^n` for some `δ < 1` | `SawinBound` | `Examples/GroupTensorBarrier.lean` | AVW Corollary 6.1 and Theorem 6.1 (`Examples/GroupTensorBarrier.lean`), the CW-family corollary `asymptoticIndependenceNumber_gcwTable_le_of_sawinBound` (`Examples/GroupTensorCWDegeneration.lean`), and the `Ī(T_G)` sandwich `avw_groupCoefficients_independence_sandwich` (`Examples/GroupTensorIndependenceLower.lean`); no other consumer. No Lean source exists and none is expected. **Erratum: `SawinBound` is false for the trivial group**, and the `Prop` is stated so that this is visible |
| Concrete global constituent type counting | identification of the paper's nested support-restricted types and hashing competitors | `ConcreteGlobalConstituentTypeCounting` | `MatrixMultiplication/CurrentProofObligations.lean` | legacy `Counted` boundary: `omega_lt_2369661_of_proof_obligations`, `omega_lt_236999_of_volumeOnly_proof_obligations`, `omega_lt_236965963_of_proof_obligations`; not an obligation of the canonical Total-Weight theorem |
| Compatibility zeroing and hole repair | the concrete recursive-block instantiation of the proved pooled-all compatibility adapter | `CompatibilityZeroingAndHoleRepair` | `MatrixMultiplication/CurrentProofObligations.lean` | legacy `Counted` boundary: the same three endpoints; not an obligation of the canonical Total-Weight theorem |
| Certified parent-consistency instantiation | identification of the generated tables with the reconstructed node probability vectors | `CertifiedParentConsistencyInstantiation` | `MatrixMultiplication/CurrentProofObligations.lean` | legacy `Counted` boundary: `omega_lt_2369661_of_proof_obligations`, `omega_lt_236965963_of_proof_obligations` only; not an obligation of the canonical Total-Weight theorem |
| Certified two-letter instantiation | the two-letter certificate adapter for the legacy `2.36965963` target | `CertifiedTwoLetterInstantiation` | `MatrixMultiplication/CurrentProofObligations.lean` | `omega_lt_236965963_of_proof_obligations` only |
| Exact level-four reconstruction | exact/interval reconstruction of the dyadic level-4 certificate `7a255f50…` | `ExactLevelFourReconstruction`, `VolumeOnlyLevelFourReconstruction` | `MatrixMultiplication/CurrentProofObligations.lean` | `ExactLevelFourReconstruction`: `omega_lt_2369661_of_proof_obligations`, `omega_lt_236965963_of_proof_obligations`; `VolumeOnlyLevelFourReconstruction`: `omega_lt_236999_of_volumeOnly_proof_obligations`, `omega_lt_236999_of_subexponentialVolumeSequence`; none is an obligation of the canonical Total-Weight theorem |
| Total-Weight sequence datum and reconstruction | a `SubexponentialLaserVolumeSequence` for `CW_5^{⊗8}` (stride, subexponential loss, per-stage direct-sum degenerations, copy/volume growth) — or, for the `_of_wholeConstituentSequenceData` form, a `WholeConstituentLaserVolumeSequenceData` whose whole-constituent stages supply those degenerations — together with the combined inequality `TotalWeightCertificateReconstruction retained volume` (`0 < M_vol ∧ rankBudgetUpper < E + 2.365815·M_vol`) | hypotheses of `omega_lt_2365815_of_subexponentialVolumeSequence` and `omega_lt_2365815_of_wholeConstituentSequenceData` (a structure-typed datum and a `Prop`; not named `Counted` obligations) | `MatrixMultiplication/CurrentProofObligations.lean` | the conditional `2.365815` endpoint only. No Lean term currently supplies either hypothesis. The fixed leg-map route to the datum is obstructed: the canonical 90df certificate's interior (ordered-half-total) and boundary (literal-word) readers cannot be realized by one leg-local label, `no_legLocalLabel_preserves_pairedTotalWeightA5_mixedKernels` (`MatrixMultiplication/PairedTotalWeightA5MixedKernelNoGo.lean`), which itself proves no exponent statement |

Nothing in the first five tables depends on any row of this table. Every conditional theorem carries
its obligation in its own statement — for instance `two_lt_coordinateGalacticExponent_groupCoefficients_of_sawinBound`
takes `SawinBound G` as an argument, and `omega_lt_2369661_of_proof_obligations` takes the paper
bridges as arguments, while `omega_lt_2365815_of_wholeConstituentSequenceData` takes
`TotalWeightCertificateReconstruction` and the whole-constituent sequence data as arguments.

*Retired.* `SliceRankDegenerationMonotone` (semicontinuity of slice rank under all polynomial
degenerations, Tao–Sawin 2016 Corollary 2 = Alman 2019 Proposition 5.1) was on this list and is
now **proved**, in `Tensor/SliceRankSaturation.lean` — see the universal-method table above. The
`Prop` definition remains in `Tensor/SliceRankDegeneration.lean` only as the universe-explicit
packaging of the statement, and every theorem that still takes it as a hypothesis has an
unconditional companion that discharges it with `sliceRankDegenerationMonotone_holds`.

### Conditional endpoints (not results)

**None of the theorems in this table is a result.** Each is an `omega K < …` statement whose
conclusion rests on hypotheses that no term in the tree supplies — a structure-typed datum, an
unproved `Prop`, or an ad hoc estimate — so on its own none of them bounds `ω`. The unconditional
bounds are exactly the ones in the Results tables above, and the strongest of them is
`ω < 2.374631`. The one family that is no longer open is marked as such in the Status column: it is
the Duan–Wu–Zhou assembly chain whose hypotheses the unconditional endpoint discharges.
This table classifies the main `omega_lt_<target>_of_*` families; any `omega_lt_*` declaration
that is not in the Results tables above is conditional, whether or not it is listed here. It is
grouped by target, one row per module family;
the named `Prop` obligations of the `2.365815` / `2.369661` / `2.36965963` endpoints are in the
preceding table instead. Module paths are at the repository root except for the `Examples/` ones,
which are under `AlgebraicComplexity/`.

| Target | Declaration(s) | Module | Conditional on | Status |
| --- | --- | --- | --- | --- |
| `ω < 2.374631` | `omega_lt_2374631_of_dwzLevelTwoAssembledStage`, `_of_countingStage`, `_of_dwz63CountingStage`, `_of_countingStageAt`, `_of_countingStageAt_true`, `_of_dwz63CountingStageAt` | `Examples/DuanWuZhouLevelTwoGlobal.lean`, `…GlobalStage.lean`, `…GlobalStageRate.lean` | the named `Prop`s `DwzLevelTwoAssembledStage` / `DwzLevelTwoCountingStage` (the count side of §6.3), plus `0 < ambient` and, in the abstract forms, the rank budget `R̃(sym₆ T) ≤ 64^6 = 68719476736` | superseded by the unconditional `omega_lt_2374631` |
| `ω < 2.374631` | `omega_lt_2374631_of_openEstimates`, `_of_openEstimatesSharp`, `_of_openEstimatesMarked` | `Examples/DuanWuZhouLevelTwoIntegration.lean`, `…IntegrationSharp.lean`, `…IntegrationMarkedFamily.lean` | the open estimate group: `hcompat` (compatibility soundness), the incidence budgets `hbudgetY`/`hbudgetZ`/`hhalf`, the certified leg-fiber degree `hsharp`, the marked-count rate `hrate`, the constituent value `hconstituent`, and a subexponential `lossHash` | superseded |
| `ω < 2.374631` | `omega_lt_2374631_of_plainOpenEstimates`, `_of_plainStageAndLeaf`, `_of_plainSymSixStage`, `_of_plainLegwiseAndLeaf`, `_of_plainSymSixStageAt`, `_of_plainBatchedStageAndLeaf` and its `_margin`, `_marked`, `_markedLoss`, `_seeded`, `_seeded_loss`, `_joint` variants, `_of_plainLinearBatchedStageAndLeaf`, `_of_dwzLevelTwoAssembledStageData`, `_of_countingStageAtData`, `_of_dwz63CountingStageAtMargin`, `_of_plainSymSixStageMargin` | `Examples/DuanWuZhouLevelTwoPlainOpenIntegration.lean`, `…PlainBatchedEndpoint{,MarginVariant,Marked,MarkedLoss,Seeded,SeededLoss}.lean`, `…PlainBatchLoss.lean`, `…IsolatedSumRate.lean` | the tensor-side stage `hstage` (or the `Z`-leg `hlegwise`, documented as discharged nowhere in the tree), the batching bound `hbatchCard`, the leaf value `hleafWeight`/`hleafValue`, and a subexponential batch loss — all quantified over every 3AP-free `B` and every seed | superseded |
| `ω < 2.374631` | `omega_lt_2374631_of_dwz63IsolatedSum`, `_of_weightedRestriction`, `_of_dwz63IsolatedSum_cofinalIndex`, `_of_dwz63IsolatedSumAt`, `_of_dwz63StageFamily`, `_of_dwz63EngineData`, `_of_dwz63CofinalEngineData`, `_of_dwz63JointHash` | `Examples/DuanWuZhouLevelTwoIsolatedBypass.lean`, `…CofinalIndex.lean`, `…IsolatedSumRate.lean`, `…StageFamily.lean`, `…InstanceData.lean`, `…LeafBookkeeping.lean`, `…TensorSideEndpoint.lean` | an isolation or stage restriction of `sym₆(CW_6^{⊗2})^{⊗n}` onto a direct sum, a `HasTauWeight` for every retained constituent at `dwz63Tau`, a copy count against `dwz63TrueCopyRate` and a value floor `exp dwz63LogVal`, all up to a subexponential loss | superseded |
| `ω < 2.374631` | `omega_lt_2374631_of_seededPeriod`, `_of_seededPeriod_goodBatchLoss`, `_of_orbitRowsSevenTen_and_seededPeriod`, `_of_referenceLeafWeight_marked`, `_of_referenceLeafWeight_marked_seeded_loss` | `Examples/DuanWuZhouLevelTwoAssemblyOrbitClosure.lean`, `…AssemblyRowSix.lean`, `…AssemblyMarked.lean`, `…AssemblyMarkedSeededLoss.lean` | the §6.2 assembly's remaining inputs: the marked reference frame, the orbit rows `6`, `7`, `10`, and the per-period good seed `hseededPeriod` | **live scaffolding, now discharged** — this is the chain the unconditional `omega_lt_2374631` composes, through `omega_lt_2374631_of_seededPeriod_applied` and `dwz63_exists_seededPeriod` |
| `ω < 2.36999` | `omega_lt_236999_of_volumeOnly_proof_obligations`, `omega_lt_236999_of_subexponentialVolumeSequence` | `MatrixMultiplication/CurrentProofObligations.lean` | the named obligation `VolumeOnlyLevelFourReconstruction` (preceding table), resp. a `SubexponentialLaserVolumeSequence` for `CW_5^{⊗8}` at the floors `E ≥ 8.2` and `M_vol ≥ 6.0165` | superseded — the `eab2c7ae…` certificate's retained side is refuted |
| `ω < 2.36999` | `omega_lt_236999_of_subexponentialVolumeSequence`, `_of_wholeConstituentSequenceData`, both `…_acceptanceFloors` forms, `…_outer_inner_floors` | `MatrixMultiplication/TotalWeightVolumeEndpoint.lean` | a `SubexponentialLaserVolumeSequence` (or `WholeConstituentLaserVolumeSequenceData`) for `CW_5^{⊗8}` plus the `e798` `Reconstruction`, resp. `AcceptanceReconstruction` (`retained ≥ 411/50`, `volume ≥ volumeFloor`) | superseded — the `e7987d7f…` rows share the mixed-reader defect. Note the name collision with the `CurrentProofObligations` theorem in the row above |
| `ω < 2.36999` | `omega_lt_236999_of_nestedSequenceData`, `_of_nestedAcceptanceData`, `_of_levelFourCanonicalInner`, `_of_levelFourEmbeddedCanonicalInner`, `_of_subexponentialVolumeSequence_acceptance_anyStride`, `_of_levelFourOuter_innerLeaf`, `_of_levelFourOuter_constantInnerLeaf` | `MatrixMultiplication/TotalWeightLeanEndpoint.lean`, `…LevelFourInner.lean`, `…LevelFourEmbeddedInner.lean`, `TotalWeightLevelFourInnerGrowthDatum.lean` | a depth-four `CWTotalWeightLocalizedOuterSequenceData` for `CW_5^{⊗8}` at stride `38`, a canonical or sparse embedded inner datum, the `C′` floors `6.4772` / `1.7428` / `volumeFloor`, and the coarse-type alignment equations | superseded (retired `C′` route). `_of_levelFourOuter_constantInnerLeaf` is additionally **vacuous**: its `hn` forces `profileMass = 19` against `count_pos`'s `≥ 6^16` |
| `ω < 2.36999` | `omega_lt_236999_of_subexponentialVolumeSequence_acceptance`, `…_acceptance_split`, `…_acceptance_of_le` | `MatrixMultiplication/TotalWeightAcceptanceFloors.lean` | a sequence at the `C′` acceptance floors `retained ≥ 411/50 = 8.22` and `volume ≥ 15021/2500 = 6.0084`, stride `38` | superseded (retired `C′` route); nothing supplies the sequence |
| `ω < 2.36999` | `omega_lt_236999_of_named_inputs`, `_of_named_inputs_levelTwo`, `_of_levelTwoEmbeddedCanonicalInner`, `_of_inner_inputs` | `MatrixMultiplication/TotalWeightAcceptanceAssembly.lean`, `…AssemblyLevelTwo.lean`, `…AssemblyLevelTwoEndpoint.lean` | the named records `SparseInnerInput`, `OuterFloorInput`, `OuterCountInput`, `LevelTwoTableInput` | **vacuous**: `OuterCountInput` is proved empty at every depth by the outer X-word ceiling above, so these prove nothing. Their own module headers mark them DORMANT and negative regression artifacts, and say they must not be cited as a record |
| `ω < 2.36999` | `omega_lt_236999_of_volumeLossSequence`, `…_at_floor`, `omega_lt_236999_of_eventualStages`, `…_at_floor`, `omega_lt_236999_of_eventualStageFamily` | `MatrixMultiplication/TotalWeightVolumeLossEndpoint.lean`, `TotalWeightEventualVolumeLossEndpoint.lean`, `TotalWeightEndpointComposition.lean` | a `SubexponentialLaserVolumeLossSequence`, resp. an `EventualWholeConstituentLaserVolumeLossData`, for `CW_5^{⊗8}` at retained floor `8.241973` and nominal volume `6` | superseded (retired composition route); audited only in `AxiomAuditCertificate/` |
| `ω < 2.36999` | `omega_lt_236999_of_sequence_at_stageFloor`, `_of_totalWeightTrackResidual`, `…_at_floor`, `omega_lt_236999_of_mergedStageFamily_at_floor` | `MatrixMultiplication/SimplifiedSequencePackaging.lean`, `MergedLeafBudget.lean` | the residual `TotalWeightTrackResidual`; resp. `RetainedCountValid` at floor `8.241973` together with a merged whole-constituent stage family clearing the per-leg budgets `(225, 227, 232)` | superseded; the residual cannot be supplied by the frozen `e798` rows |
| `ω < 2.36999` | `omega_lt_236999_of_compressionSeam` (two distinct theorems of that name) | `MatrixMultiplication/SimplifiedRetainedCompressionSeam.lean`, `TotalQuotientRetainedCompressionSeam.lean` | the extraction sequence plus `RetainedCompressionSeam retained` — a `Prop` whose evaluation half the module leaves open — and a volume floor | superseded; audited only in `AxiomAuditCertificate/` |
| `ω < 2.36588731` | `omega_lt_236588731_of_subexponentialVolumeSequence`, `_of_wholeConstituentSequenceData` | `MatrixMultiplication/TotalWeightVolumeEndpoint.lean` | the sequence datum plus the `e798` `Reconstruction` (generated retained and volume witnesses) | superseded — `e7987d7f…` is refuted, not merely unproved |
| `ω < 2.36588731` | `omega_lt_236588731_of_compressionSeam` | `MatrixMultiplication/TotalQuotientRetainedCompressionSeam.lean` | the sequence datum, `RetainedCompressionSeam`, and `volume ≥ scalarCoordinateSum/3` | superseded; audited only in `AxiomAuditCertificate/` |
| `ω < 2.363145`, and `ω < 2.36315` | `omega_lt_2363145_of_subexponentialVolumeSequence`, `omega_lt_236315_of_subexponentialVolumeSequence` | `MatrixMultiplication/SortedPairVolumeEndpoint.lean` | a `SubexponentialLaserVolumeSequence` for `CW_5^{⊗8}` plus `Reconstruction`, i.e. `E ≥ 8.25847` and `M_vol ≥ 6.0091` | superseded — the sorted-pair diagnostic is rejected (it double-counts the `E2` resource) and nothing in the tree supplies the floors |
| `ω < 2.369837225` | `omega_lt_2369837225_of_subexponentialVolumeSequence` | `MatrixMultiplication/SimplifiedSharpEndpoint.lean` | the sequence datum plus `Reconstruction`: the generated `retainedExponentLowerWitness` and `volume ≥ 6.016717904289` | superseded — the sharp form of the refuted `eab2c7ae…` track |
| `ω < 2.369837225` | `omega_lt_2369837225_of_compressionSeam` | `MatrixMultiplication/SimplifiedRetainedCompressionSeam.lean` | the sequence datum, `RetainedCompressionSeam`, and `volume ≥ SimplifiedSharpEndpoint.volumeFloor` | superseded; audited only in `AxiomAuditCertificate/` |

## Build

```bash
lake build
```

The default build checks the reusable `AlgebraicComplexity` library. The repository defines eight
Lake targets:

- `AlgebraicComplexity` (the default): the reusable core library;
- `AlgebraicComplexityClients`: the classical regression clients (Strassen, Schönhage, and the
  Coppersmith--Winograd analyses);
- `AlgebraicComplexity.DuanWuZhouLevelTwo`: the Duan--Wu--Zhou level-two tier, its own target so
  that core edits do not rebuild it;
- `MatrixMultiplication`: the paper-specific development and its proof-obligation boundary;
- `MatrixMultiplicationCertificate`: the opt-in generated exact certificate checker; its cold build
  compiles about 10,500 generated modules and takes many hours;
- `AxiomAudit`: the enforcing axiom audit over the ordinary libraries;
- `AxiomAuditCertificate`: the same audit for the declarations inside the generated certificate;
- `Frontier`: the leaderboard's statement anchor, a leaf no library depends on.

Regression clients and the paper-specific development are separate targets so that ordinary core
edits do not rebuild every large certificate. To check everything except the opt-in generated
certificate in one command:

```bash
lake build AlgebraicComplexity AlgebraicComplexityClients MatrixMultiplication AxiomAudit Frontier
lake build AxiomAuditCertificate     # opt-in; covers the generated certificate
```

The axiom audit is enforcing rather than advisory: the `AxiomAudit` target compiles
`AxiomAudit.lean` together with every module under `AxiomAudit/` (its `AxiomAudit.*` glob), which
run `#assert_axioms` on the literature-facing theorems (the counts are in `## Results`
above), and the build fails if any audited declaration depends on an axiom outside `propext`,
`Classical.choice`, and `Quot.sound`.

The complementary hard trust scan fails if any committed Lean source under `AlgebraicComplexity`,
`AlgebraicComplexityClients.lean`, or `MatrixMultiplication` contains `sorry`, `admit`, or a
declared `axiom`. It also rejects opaque declarations outside `MatrixMultiplication/Generated/`
and generated opaque declarations without an explicit body. Accepted generated occurrences are
counted rather than listed; `rg -n '^\s*opaque\b' MatrixMultiplication/Generated -g '*.lean'`
lists them:

```bash
bash scripts/trust_scan.sh
```

The current hard scan passes. It matches `sorry` and `admit` as bare words and matches `axiom`
only in declaration position, so reviewed documentation about named proof obligations does not
create a false CI failure.

The reusable tensor boundary and source/documentation coverage have separate enforcing checks:

```bash
bash scripts/check_tensor_boundary.sh
bash scripts/check_source_coverage.sh
bash scripts/check_module_docs.sh
```

The boundary gate checks every file under `Tensor/`; its five pre-existing mixed-layer edges are
explicitly grandfathered, so any new leak fails.  The coverage gate blocks new Lean sources
outside every public or audit target, against the may-only-shrink list
`scripts/source_coverage_grandfathered.txt` (166 tracked sources are still exempt from it), and
the module-doc gate requires a human-readable overview in every hand-written file.

`.github/workflows/ci.yml` runs the static gates on every push to `main` and every pull request —
ten enforcing steps (the four above plus copyright headers, `#assert_axioms` targets, the `decide`
budget, the heartbeat governor, certificate-table wiring and artifact provenance) and a warn-only
declaration-collision scan; its trust-scan job is the authority for the list. They are followed by
`lake build AlgebraicComplexity AlgebraicComplexityClients MatrixMultiplication AxiomAudit
Frontier` through `leanprover/lean-action`, with both the Mathlib olean
cache and the GitHub `.lake` build cache enabled explicitly so that a pull request never recompiles
Mathlib. That audit target's `AxiomAudit.*` glob includes `AxiomAudit.CensusAll`, whose
`#axiom_census` walks `Environment.constants` and fails the build if any module of this repository
declares an `axiom` or reaches one outside the allowlist. The census is the *authority* for the
trust policy and `scripts/trust_scan.sh` is a fast pre-filter, because Lean's command parser is
whitespace-insensitive: a mid-line `axiom` compiles while evading a line-anchored regex, but not a
walk over what the kernel accepted.

Two more jobs cover the generated certificate targets (`MatrixMultiplicationCertificate`,
`AxiomAuditCertificate`, including `AxiomAuditCertificate.Census`). `certificate-smoke` builds a
slice of them on every push and pull request: every `AxiomAuditCertificate` audit except the six
that reach the level-four analytic tables, plus two modules of those tables
(`scripts/certificate_smoke_targets.sh`). `certificate` builds the full tier, about 11,000 modules
and roughly 14 hours on a 2-core hosted runner, so a hosted run ends at the six-hour job limit; it
runs only on a manual run (Actions → CI → Run workflow) and on a pull request labelled
`record-claim`, and a complete build needs a larger runner or a local machine. Branch protection,
required checks, and the automated-review settings that cannot be configured from inside the
repository are listed in `.github/BRANCH_PROTECTION.md`; `.github/CODEOWNERS` marks the files that
decide what CI checks at all. The `Frontier` statement anchor is built on every run and sits inside
the census closure, and after the build a pull request that moves `Frontier.frontierConstant` must
have Lean itself confirm `new + Frontier.recordDelta ≤ old` in exact rationals, with `recordDelta =
1/100000` (`scripts/check_frontier_improvement.sh`). The focused audits that still reach generated
chunks transitively are listed in `scripts/heavy_audit_grandfathered.txt`, which is the authority
for that set; their move into the opt-in audit target is still pending.

On a shared or memory-constrained machine, run public builds through
`scripts/lake_build_serial.sh ...`. It adds a worktree lock, refuses to overlap a raw Lake writer,
sets `LEAN_NUM_THREADS=1`, and lowers process priority. The package also passes `-j 1` to each Lean
compiler. Its `-M 8000` setting is an allocation guard on Lean's memory footprint, not an expected
resident-memory figure; the earlier `-M 768` and `-M 3000` settings aborted on some layer-3 imports
and kernel checks.

### Building from scratch

Nothing is assumed but `git`: `elan` installs the exact pinned compiler.

```bash
curl -sSf https://elan.lean-lang.org | sh -s -- -y   # Lean's toolchain manager, once per machine
git clone https://github.com/thomasahle/matrix-multiplication.git
cd matrix-multiplication
lake exe cache get                                   # download Mathlib's prebuilt oleans
lake build AlgebraicComplexity AlgebraicComplexityClients MatrixMultiplication AxiomAudit Frontier
```

`elan` reads `lean-toolchain` and fetches exactly `leanprover/lean4:v4.33.0-rc1`;
`lake-manifest.json` pins the Mathlib and CSLib commits, so a build never resolves a moving
dependency. Do not skip `lake exe cache get`: it downloads roughly 8,500 compiled Mathlib modules,
while compiling Mathlib from source takes hours and is never necessary.

**What to expect.** `lake exe cache get` is a few minutes on an ordinary connection. This
repository's own modules have no download cache, so a first local build compiles all of them from
source; budget an hour or more. The targets overlap heavily, so building all of them costs
little more than the largest. Afterwards Lake recompiles only what an edit reaches. In CI the fixed
overhead is about 70 seconds — in one measured run, 49 s restoring the `.lake` cache, 14 s
resolving pinned dependencies, 5 s for the Mathlib cache — after which only the modules a commit
invalidated are recompiled. A pull request restores that cache from its base branch, which is why
`main` must keep running CI: see `.github/BRANCH_PROTECTION.md`.

**Memory, not CPU, is the binding constraint.** `lakefile.toml` passes `-M 8000 -j 1` to every Lean
process: an 8 GB guard on Lean's memory footprint, one worker each. Most modules need far less —
several import closures cross 2.5–3 GB before elaborating their first declaration — but some
kernel checks and generated tables need more than 3 GB, and a footprint runs well above resident
memory. Lake 5 has no `-j` option of its own; the number of Lean processes it runs concurrently is
`LEAN_NUM_THREADS`, so that variable is the memory dial. CI sets `LEAN_NUM_THREADS: 2` on a 16 GB
runner; on a 16 GB workstation use at most `LEAN_NUM_THREADS=2`, or `LEAN_NUM_THREADS=1` via
`scripts/lake_build_serial.sh` when the machine is shared. Leaving it unset lets Lake use every
core, i.e. one `-M 8000` process per core.

## Reusable library

The paper-independent tensor foundation is the `AlgebraicComplexity/Tensor/` directory, reached
through `AlgebraicComplexity.lean`. `AlgebraicComplexity/Tensor.lean` is its stable entry point for
downstream users; it is not a separate Lake target and no module of the tree imports it, and it
deliberately leaves out the `Tensor/` modules that bridge into layer 2. What holds the layer
together is the enforcing boundary gate: a source under `Tensor/` may import only
`AlgebraicComplexity.Tensor.*` and the asymptotics leaves, with five grandfathered bridge edges:
`Tensor/TypeExtraction.lean`
imports `Combinatorics.WordType`, and `Tensor/IndependenceBlockEntropy.lean` imports
`Analysis.Subexponential`, `Combinatorics.WordType`, `Probability.EntropyValue` and
`Probability.Finite`. Apart from those, the layer carries no matrix-multiplication exponents,
numerical certificates, or named paper clients, which is what makes it the intended starting
surface for downstream users and a future CSLib contribution.

Its tensorial-relation API is parameter-generic. The optional point-mass specialization for
`ProbabilityVector` lives in `AlgebraicComplexity/Probability/TensorialRelation.lean`, so clients
can use weight-indexed repeated orientations without introducing a probability dependency into
the reusable tensor umbrella.

Per-module content is not inventoried here: the `## Module map` below lists what each layer
contains, `DESIGN.md` §Layering carries the layer-by-layer description, and its §Core
representation choices records the separation of abstract `PiTensorProduct` tensors (used for
structural theorems) from finite coordinate spaces and explicit lists of terms (used for
executable certificates).

## Regression clients

The exponent bounds, declaration names, and hypotheses of every client are in the `## Results`
tables above and are not repeated here. What the tables do not record is the shape of each
client and the two modules that carry no headline bound of their own:

- `Examples/Strassen.lean`, `Examples/Laderman.lean`, `Examples/HopcroftKerrUpper.lean`,
  `Examples/DiscoveredDecompositions.lean`: closed finite coefficient certificates, kernel-checked
  once over `ℤ`, with the generic cast theorem `MMCertificate.rankLE_of_intCoefficient` carrying
  them to every commutative ring — except `DiscoveredDecompositions`, whose two theorems are
  certified only over commutative rings with `2 = 0` (plus the `ZMod 2` instances), as its table
  row records. The `DiscoveredDecompositions` module documentation records that the AlphaTensor and
  AlphaEvolve factor tables are deliberately absent, because they are not in the repository's
  local sources.
- `Examples/Bini.lean` and `Examples/Schonhage.lean`: explicit approximate/degeneration
  certificates fed to the proved partial τ-theorem and asymptotic sum inequality respectively.
- `Examples/Compression.lean`: the smallest nontrivial full-cube symmetrization — two copies in
  each of three cyclic orientations give eight independent scalar products, which the elementary
  rank-eight algorithm compresses to one `2 × 2` product. A regression against accidentally
  keeping only the two diagonal products.
- `Examples/CoppersmithWinograd.lean` and `CoppersmithWinogradPartition.lean`: the `q + 2`
  polynomial pure tensors whose degree-five leading coefficient is `CW_q`, the corner-removing
  diagonal monomial degeneration, and the genuine typed six-block partition, whose direct-sum
  realization is proved canonically isomorphic to the original coordinate tensor with all six
  constituents certified as the expected rectangular tensors and their volumes matched to the
  support-level entropy model.
- `Examples/CoppersmithWinogradFirstPower{,Hashing}.lean` and
  `CoppersmithWinogradEasyHashing.lean`: the complete classical laser pipeline — exact rational
  joint and marginal types, semantic variable zeroing, typed-fiber competitor bounds, one-pass
  isolation on all three legs, prime-field Behrend hashing (Bertrand's postulate and Mathlib's
  Behrend construction supply the fields and progression-free sets), a direct sum of equal square
  matrix-multiplication tensors, Schönhage's inequality, and removal of every subexponential loss.

The two numerical CW targets (`2.41`, `2.3872`) come from exact-rational atanh certificates; the
other exponent bounds are symbolic logarithm inequalities or exact integer/rational power
comparisons. No client takes floating-point input. The older named tight-support and
extraction-rate propositions survive as reusable interfaces and are *not* premises of any headline
(unconditional) theorem — the conditional companions
`coppersmithWinograd_firstPower_omega_lt_of_{laserConclusion,tightSupport,extraction}` do keep them
as explicit hypotheses — and none of these clients depends on unpublished optimization data.

## Lower bounds and barriers

### Classical rank lower bounds

Everything in this group is proved over an arbitrary field, with no proof obligation; the
declaration names are in the rank/border-rank table of `## Results` above. Three architectural
notes that the table cannot carry:

- `Examples/BlaeserLowerBound.lean`'s `2n² − n ≤ rank ⟨n,n,n⟩` is the first bound in the tree
  whose leading coefficient beats flattening for every `n`. Bläser's `5/2·n²` needs the sandwich
  normal form at scale, and the module records that as a named obstruction rather than a claim.
- `MatrixMultiplication/KoszulBorderRank.lean` gives an explicit kernel-checked `p = 1` Koszul
  flattening of `⟨2,2,2⟩` with its sixteen-element biorthogonal system. The Landsberg--Ottaviani
  statement it belongs to is about *border* rank; the border version is blocked on `K[ε]`
  exterior-power base change and is documented as such rather than claimed.
- `Tensor/SliceRank.lean` supplies the finite core of the universal-method `S̃` barrier
  (`S̃(⟨q⟩) = q`) and of the comparison chain `I ≤ subrank ≤ sliceRank ≤ rank`. In the AVW `Ī`
  program slice rank is deliberately *not* the barrier quantity: it is neither submultiplicative
  nor monotone under passing to sub-supports, and `BARRIER_FRAMEWORK.md` §1 records why that
  decides the architecture. The universal-method half does use the asymptotic slice rank `S̃`
  directly, as a `limsup` (`Tensor/AsymptoticSliceRank.lean`,
  `MatrixMultiplication/UniversalSliceRankBarrier.lean`); see the universal-method table above.

### The AVW barrier program

The framework is that of Alman and Vassilevska Williams, *Limits on all known (and some unknown)
approaches to matrix multiplication*, arXiv:1810.08671. `BARRIER_FRAMEWORK.md` is the contract:
it fixes the definitions, the module graph, and milestones A--N. The statuses below are those
recorded in its §6; the per-theorem declaration names, constants, and hypotheses are in the
barrier tables of `## Results` above, and are not repeated here.

| Milestone | AVW result | Status |
| --- | --- | --- |
| A | powers of `I`, supermultiplicativity, basis-dependence witness | proved |
| B | `Ī` via the Fekete engine, `Ī(T^{⊗k}) = Ī(T)^k` | proved |
| C | Lemma 4.3 and Corollaries 4.1--4.2, on the degenerated table | proved |
| D | Definition 4.1 / Lemma 4.1: the Galactic exponent `ω_g` and `omega ≤ ω_g` | proved, under the equal-dimension reading of Lemma 4.1 |
| E | Lemma 4.2 (Strassen weights) and Lemma 4.4 | proved: `Ī⟨m,n,p⟩ = mnp/max`, exact for all dimensions |
| F | Theorem 4.1 and Corollary 4.3 | proved, for the *coordinate* Galactic exponent |
| G | Definition 5.2, Claim 5.1, Theorem 5.3 | proved, for covers and with no polynomial loss |
| H | Lemma 5.1, the binomial tail | proved by the method of types, no measure theory |
| I | Theorem 5.2 and Corollary 5.1, the corner-term barrier | proved, with explicit `cornerExponent q` |
| J | Theorem 5.1, the splitting bound | proved, including both AVW numerical certificates |
| K | Lemmas 7.1, 7.2 and **Theorem 7.1** | proved in full |
| L | Lemma 6.1, Corollary 6.1, Theorem 6.1 | Lemma 6.1 proved as an equality; Theorem 6.1 conditional on the named obligation `SawinBound` |
| M | Theorems 7.2, 7.3, 7.4 | Theorem 7.2 proved; 7.3 proved (`avw_theorem_seven_three`, with the stronger `(27/4)q² ≤ Ī³` and Remark 7.2 for q ≥ 2); 7.4 proved for **every** finite group of order `≥ 2` (`avw_theorem_seven_four`, `avw_theorem_seven_four_exists_of_two_le`), with certified small-order values `Ī(T_{C₂}) ≥ 1.84`, `≥ 2.629` at order 3, `≥ 3.31` at order 4 |
| N | Theorems 7.5, 7.6 | 7.5 proved (`avw_theorem_seven_five`, explicit constant `6/(3 − cornerExponent q)`); 7.6 proved (`avw_theorem_seven_six`, explicit constant `diagonalExponent q`) |

The headline is `avw_theorem_seven_one` in
`Examples/GeneralizedCoppersmithWinogradBarrier.lean`, for every field `K`, every `q`, and every
permutation `σ` — that is, for every generalized Coppersmith--Winograd tensor of Definition 3.1.
What the table row does not record is how it is assembled: three overlapping regimes are proved
separately and combined — `q ≤ 5` through Corollary 5.1 (`avw_lemma_seven_one`), `6 ≤ q` through
Theorem 5.1 (`avw_lemma_seven_two_of_six_le`), and `24 ≤ q` through Theorem 5.3
(`avw_lemma_seven_two`) — with the `6 ≤ q` splitting constant `60000/29999 = 2 + 2/29999` the
binding branch (`avwTheoremSevenOneConstant_eq`); the `q = 5` corner value
`6/(3 − cornerExponent 7)` lies above it. The constant is certified by exact
rational arithmetic and the atanh log enclosures of `Analysis/Log.lean`; no numerical bound is
taken from floating point.

The Section 6 group-tensor results are in `Examples/GroupTensorBarrier.lean` and
`Examples/CoppersmithWinogradGroupExclusion.lean` (the Section 7.2 degeneration is the one in
`Examples/GeneralizedCoppersmithWinograd.lean`); their statements are in the barrier table
above. The one point that belongs here rather than in a table: Sawin's theorem has no Lean source
and no realistic prospect of one, so `SawinBound` is a plain `Prop` definition exposed as an
explicit hypothesis of Theorem 6.1, per the named-proof-obligation policy of `DESIGN.md`. It is
never an `axiom`, never a typeclass instance, and never reported as proved.

### Corrections to the literature found by the formalization

Formalizing the AVW framework turned up six places where the printed statements need amending.
Each correction is recorded in `BARRIER_FRAMEWORK.md` and in the relevant module documentation,
and in each case it is the corrected statement that is formalized.

- **Lemma 4.2 is a statement about the degenerated table.** The minimum-weight triples of
  `⟨a,b,c⟩` under Strassen's weights are *not in general* an independent set of `⟨a,b,c⟩`'s own
  coefficient table: for `⟨3,3,3⟩` at level 3 the closure clause of the definition fails. The
  formal witness is `not_independentSet_mmCoefficients_mmMinWeightSupport`. The correct reading
  is that the independent set lives in the degenerated table `D`, and Lemma 4.3 (milestone C) must
  be phrased on `D` as well.
- **Theorem 4.1 bounds the coordinate Galactic exponent.** `Ī` is basis-dependent — over `ℚ` the
  legwise change of basis `[[1,1],[1,−1]]` sends `⟨2⟩`, with `I = 2`, to a table with `I = 1`
  (`HadamardWitness.independenceNumber_not_isomorphism_invariant`). Since the abstract Galactic
  exponent is an infimum over all coordinate presentations, what Theorem 4.1 actually bounds is
  the exponent of a coordinate certificate. `galacticExponent_le_coordinateGalacticExponent` is
  proved, for tables with at least one coordinate certificate; the reverse is not expected. AVW
  conflate the two.
- **Lemma 7.2's part measure is `(q+1)²`, not `q²`.** With AVW's own displayed parts the three
  measures are `q²`, `(q+2)²` and `(q+1)²`, not `q²` each. Moving the single term `x₀y₀z₀` from
  `T₂` to `T₁` balances them at minimal variable sets of sizes `1, q+1, q+1`, i.e. `μ = (q+1)²`
  each, so Theorem 5.3 gives `Ī(T) ≤ 3(q+1)^{2/3}`. Their printed inequality `3q^{2/3} < q^{0.997}`
  is correct as arithmetic but compares against the wrong base — what Corollary 4.3 needs is a
  comparison against `R̃(T) ≥ q+2`. The corrected chain is what is formalized, and the conclusion
  survives.
- **`SawinBound` is false for the trivial group.** The `Prop` is stated so that this is visible
  rather than silently assumed away.
- **Corollary 5.1's second corner term is unnecessary.** One corner term already forces
  `Ī(T) < q`, with the explicit exponent `cornerExponent q = 1/(q²(q+1)² log q)`.
- **Theorem 5.3 holds with no polynomial loss.** The formalized statement is stronger than the
  printed one in three ways: it holds for covers rather than only partitions, over a plain
  `CommSemiring`, and with no polynomial loss. The proof sums over colour words and injects each
  colour class into a leg projection, so neither the greedy walk nor `IndependentSet.of_subSupport`
  is needed.

A seventh correction is a sign typo: in Theorem 7.3, AVW write that Coppersmith and Winograd show
`ω_g(CW_q) ≥ f(q)`, where the intended relation is `≤` — it is a positive result, an upper bound on
`omega` achieved by the method. Milestone M is now proved with the corrected sign, and both
directions are in the tree: `avw_theorem_seven_three` for the `Ī` lower bound and
`coordinateGalacticExponent_gcwTable_le_avwF` for `ω_g^coord(CW_q^σ) ≤ f(q)` under the hypothesis
`R̲(CW_q^σ) ≤ q+2`, discharged for `σ = id` by
`coordinateGalacticExponent_gcwTable_refl_le_avwF`. Two further errata
were found while proving it: `f(1)` is undefined, so AVW's "every positive integer `q`" must read
`q ≥ 2`; and Remark 7.2 in fact holds from `q ≥ 2` rather than `q ≥ 3`. An eighth, ours rather
than AVW's, is recorded in `BARRIER_FRAMEWORK.md` milestone M8: `R̲(CW_q^σ) = q+2` is *false*
unless `σ² = id`, which is why `genCW_borderRankLE_refl` is claimed only for `σ = id`.

## The Total-Weight framework (conditional)

The Total-Weight programme is a conditional framework for the Coppersmith–Winograd method together
with a certificate obstruction; its manuscript is in preparation and not yet public. It yields
**no new bound on `omega`**: every Total-Weight `omega_lt_*` theorem in the tree carries a datum or
`Prop` that no term in the tree supplies (see the last two tables of `## Results`), and the
strongest unconditional bound here remains `omega_lt_2374631`.

`MatrixMultiplication/CurrentProofObligations.lean` is the adapter boundary. Its canonical theorem
`omega_lt_2365815_of_wholeConstituentSequenceData` (sequence-level form
`omega_lt_2365815_of_subexponentialVolumeSequence`) derives `omega < 2365815/10^6` from an actual
`WholeConstituentLaserVolumeSequenceData` for `CW_5^{⊗8}` and the `Prop`
`TotalWeightCertificateReconstruction`, through the proved Schönhage inequality and the explicit
eighth-power `CW_5` border-rank certificate; `certified_totalWeight_endpoint_slack` checks only the
exact rational margin `3515534217/10^15`. The certificate the module names (`90dfb5ea…`) cannot
supply these hypotheses: `no_legLocalLabel_preserves_pairedTotalWeightA5_mixedKernels`
(`MatrixMultiplication/PairedTotalWeightA5MixedKernelNoGo.lean`) shows that its interior
(ordered-half-total) and boundary (literal-word) readers are not realized by one fixed leg-local
label, so it does not satisfy the framework's uniform-quotient hypothesis; that module proves no
counting, entropy, tensor-restriction or exponent statement. The legacy `Counted` endpoints kept
in the same module for source compatibility carry the named obligations tabulated above, none of
which is an obligation of the canonical theorem. `MatrixMultiplication/Q20EndpointAdapter.lean`
(`omega_lt_236999_of_q20EventualStages`) is an adapter of the same shape at target `2.36999`,
whose stage datum is likewise an explicit hypothesis constructed nowhere in the tree.
`MatrixMultiplication/FinalCertificate.lean` is the archived `2.37071` arithmetic client, and the
outer X-word ceiling (upper-bound machinery table) is a further negative result.

Proved independently of any certificate and kept as reusable library: the hashing, isolation,
compatibility-zeroing, hole-repair (`7^d` copy bound) and regional-division stages; the finite
parent-consistency/KL correction (`Probability/ParentConsistency.lean`); the conditional
method-of-types identity; nested coarsening and typed-fiber disintegration; and the
repeated-orientation theorem (`MatrixMultiplication/RepeatedOrientation.lean`). The volume-side
reconstructions (`MatrixMultiplication/SimplifiedVolumeReconstruction.lean`,
`TotalQuotientVolumeReconstructionBase.lean`) and the opt-in `MatrixMultiplicationCertificate`
target certify arithmetic only, not the quotient semantics. A bound from any of these adapters
would need a certificate that satisfies the uniform-quotient hypothesis and a formalized extraction
sequence for it; the tree contains neither.

## Next library milestones

On the upper-bound side, the remaining classical backlog is the 21-term border `⟨3,3,3⟩` APA
client and Pan-style trilinear aggregation (the converse direction of Proposition 2.7, circuits
imply rank bounds, is now proved in `MatrixMultiplication/RankComplexityConverse.lean`). These are
the tail of the theorem sequence in He and Williams's
[Cornell CS 6810 matrix-multiplication notes](https://www.cs.cornell.edu/courses/cs6810/2023fa/Matrix.pdf);
`DESIGN.md` records the complete crosswalk and current proof status. The notes guide coverage,
while primary papers determine exact statements and hypotheses.

The immediately preceding `2.371177` optimization framework is intentionally not a regression
target: its unpublished data would make the test non-self-contained. Strassen and the classical
Coppersmith--Winograd analyses provide durable public regression clients instead.

On the lower-bound and barrier side, milestones A--N of `BARRIER_FRAMEWORK.md` are all closed,
as recorded in the milestone table above and in the `## Results` tables. Theorem 7.4 covers every
finite group of order `≥ 2` (`avw_theorem_seven_four_exists_of_two_le`; the
Kleinberg--Sawin--Speyer *values*, such as `2.75510…` at order 3, are still not claimed), and
Strassen's commutation equations are proved (`Tensor/StrassenEquations.lean`), giving the negative
half of milestone M8's border-rank hypothesis as a dichotomy
(`borderRank_genCW_ge_of_not_involutive`). What remains open is the sharpening ideas collected in
the "Ideas for improving the lower bounds" section of `LOWER_BOUNDS_ROADMAP.md`. That file also
records what was explicitly descoped: Hopcroft--Kerr's general `⌈7n/2⌉` mod-two bound,
`rank ⟨2,3,3⟩ = 15`, and the full Bläser `5/2·n²`.

## Module map

By layer, following `DESIGN.md`. A lower layer is not meant to import a higher one; the
exceptions in the current tree are `Tensor/TypeExtraction.lean` and
`Tensor/IndependenceBlockEntropy.lean` (layer 1 → layer 2, the grandfathered boundary edges
above), `Combinatorics/RecursiveSplitMarginalCounting.lean` and
`Probability/ComplementaryProductProjectionParentLaw.lean` (layer 2 → layer 3), and the core
umbrella `AlgebraicComplexity.lean`, which imports one `Examples/` module.

- **Layer 0** — `AlgebraicComplexity/Asymptotics.lean`: growth rates, exponential-rate calculus,
  and the multiplicative Fekete engine. Mathlib only.
- **Layer 1** — `AlgebraicComplexity/Tensor/` (120 modules): three-legged tensors,
  restriction and isomorphism, products, direct sums, indexed families and powers; rank,
  conciseness, polynomial degeneration, border rank, asymptotic rank; coordinates and monomial
  certificates; partitioned tensors, extraction, compatibility zeroing, hole repair; and the
  lower-bound core — substitution method, Koszul flattening, slice rank (including the saturation
  proof of Tao--Sawin monotonicity and the block-entropy bounds), subrank, Strassen's commutation
  equations, the asymptotic-invariant engine, independence number and its asymptotic, measure, and
  splitting theory, and group tensors.
- **Layer 2** — `AlgebraicComplexity/Combinatorics/` (103), `Probability/` (63), `Analysis/` (49):
  word types and multinomial counting, affine hashing and progression-free filtering, the binomial
  tail by the method of types, hole-repair counting; finite probability vectors, entropy chain
  rules, Kullback--Leibler bounds, parent consistency, two-letter couplings; subexponential-loss
  calculus, proportional multinomial entropy bounds, and certified rational logarithm enclosures.
  `Adapters/CSLib/` holds the one adapter to CSLib's probability API.
- **Layer 3** — `AlgebraicComplexity/MatrixMultiplication/` (282): the rectangular
  matrix-multiplication tensor and its symmetry and product laws, the bilinear-algorithm bridge,
  the exponent, Bini interpolation, Schönhage's asymptotic sum inequality and its partial
  τ-theorem, compression and type extraction, the C-tensor, the generic laser and interface
  machinery, the rectangular exponent, and the barrier layer (Galactic method, the universal
  method and its slice-rank barrier, independent diagonal, independence barrier, mass
  distribution, coordinate block certificates, Koszul border rank).
- **Layer 4 — regression clients** — `AlgebraicComplexity/Examples/` (544 modules), reached
  through `AlgebraicComplexity/Examples.lean` (the `AlgebraicComplexityClients` target), the
  `AlgebraicComplexity/DuanWuZhouLevelTwo.lean` umbrella, the `MatrixMultiplication` targets, and —
  for the rest — the focused `AxiomAudit/` companions: Strassen, Schönhage, Bini, Laderman,
  Hopcroft--Kerr, the machine-discovered decompositions, the small lower-bound clients, the
  Coppersmith--Winograd family (partition, first power, easy variant, square, the exceptional `112`
  C-tensor), the Duan--Wu--Zhou second-power (level-two) development (218 modules), the
  Total-Weight nested-coarsening and inner-sequence clients (infrastructure, not an endpoint), the
  generalized CW tensors, and the barrier clients.
- **Layer 4 — paper development** — `MatrixMultiplication/` (183 top-level modules plus 11341
  generated ones under `MatrixMultiplication/Generated/`): the repeated-orientation theorem,
  entropy duals, dyadic and log-linear arithmetic, the simplified-exponent recurrences, the
  level-four reconstruction, the paired Total-Weight mixed-kernel obstruction
  (`PairedTotalWeightA5MixedKernelNoGo.lean`), `CurrentProofObligations.lean` with the named paper
  bridges, and the archived `FinalCertificate.lean`.
- **Audit and umbrellas** — `AlgebraicComplexity.lean`, `AlgebraicComplexityClients.lean`,
  `MatrixMultiplication.lean`, `MatrixMultiplicationCertificate.lean`, `AxiomAudit.lean`,
  `AxiomAuditCertificate.lean`, and the `#assert_axioms` command in `AxiomAudit/Command.lean`.
