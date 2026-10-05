import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 6, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk6

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 11927666333109933216324263084032
def positiveArguments : Array ℕ := #[
    1, 89091, 8210441, 2052607, 178165, 33993
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 1682881409301358246933561344, 77545422775957465435966799872, 77545299994428910825191243776, 1682720848840940678996295680, 642109615408751398996672512
  ]
def positiveScales : Array ℕ := #[
    0, 16, 22, 20, 17, 15
  ]
def negativeArguments : Array ℕ := #[
    8093471895, 731224449783, 731100613293, 8093471895, 1155524049, 40382630217,
    487230609159, 40383582021, 577779021, 745877512645, 67388122287333, 67376709774343,
    745877512645, 40382630217, 1411270344961, 17027472112847, 1411303608093, 20191909093,
    8093471895, 745877512645, 186469082915, 16185399425, 186469082915, 16847003897091,
    16844150773361, 186469082915, 487230609159, 17027472112847, 205442428227169, 17027873444211,
    243622471211, 731224449783, 67388122287333, 16847003897091, 1462309370145, 16185399425,
    1462309370145, 1462061720795, 16185399425, 40383582021, 1411303608093, 17027873444211,
    1411336872009, 20192385009, 731100613293, 67376709774343, 16844150773361, 1462061720795,
    577779021, 20191909093, 243622471211, 20192385009, 288898009, 8093471895,
    745877512645, 186469082915, 16185399425, 1
  ]
def negativeCoefficients : Array ℕ := #[
    9112439252613895532052480, 411642769945864345585975296, 411573056199586986816700416, 9112439252613895532052480, 650502209561755845132288, 22733399799690216502984704,
    274286448731496521932996608, 22733935617707682721431552, 650521345919522495791104, 419891711001506802292490240, 18968070151401894711234920448, 18964857814573824402163499008,
    419891711001506802292490240, 22733399799690216502984704, 794474574960673868409208832, 9585614632809907676998795264, 794493300439283915361878016, 22734068566783432465580032,
    9112439252613895532052480, 419891711001506802292490240, 419891046166056061024337920, 9111569852409080027545600, 419891046166056061024337920, 18968040118312080385228406784,
    18964827786570262905318539264, 419891046166056061024337920, 274286448731496521932996608, 9585614632809907676998795264, 115653805401246022194302025728, 9585840562282577988610424832,
    274294517641234747347697664, 411642769945864345585975296, 18968070151401894711234920448, 18968040118312080385228406784, 411603495905337919269765120, 9111569852409080027545600,
    411603495905337919269765120, 411533788810314260173291520, 9111569852409080027545600, 22733935617707682721431552, 794493300439283915361878016, 9585840562282577988610424832,
    794512026359246725796855808, 22734604400563497379823616, 411573056199586986816700416, 18964857814573824402163499008, 18964827786570262905318539264, 411533788810314260173291520,
    650521345919522495791104, 22734068566783432465580032, 274294517641234747347697664, 22734604400563497379823616, 650540482840239099871232, 9112439252613895532052480,
    419891711001506802292490240, 419891046166056061024337920, 9111569852409080027545600, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    32, 39, 39, 32, 30, 35,
    38, 35, 29, 39, 45, 45,
    39, 35, 40, 43, 40, 34,
    32, 39, 37, 33, 37, 43,
    43, 37, 38, 43, 47, 43,
    37, 39, 45, 43, 40, 33,
    40, 40, 33, 35, 40, 43,
    40, 34, 39, 45, 43, 40,
    29, 34, 37, 34, 28, 32,
    39, 37, 33, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 16442992077164403, 22969028282700040, 20969025998407381, 17442854425854227, 15052950069882485
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32914111574763886, 39411523354024268, 39411279005766903, 32914111574763886, 30105900139764971, 35233015828771440,
    38825813814982916, 35233049832171443, 29105942580085649, 39440147775570522, 45937559568879596, 45937315220586979,
    39440147775570522, 35233015828771440, 40360131517777909, 43952929513857427, 40360165521177913, 34233058269092118,
    32914111574763886, 39440147775570522, 37440145491277830, 33913973923440109, 37440145491277830, 43937557284586573,
    43937312936293958, 37440145491277830, 38825813814982916, 43952929513857427, 47545727488034633, 43952963517263700,
    37825856255304501, 39411523354024268, 45937559568879596, 43937557284586573, 40411385702714091, 33913973923440109,
    40411385702714091, 40411141354456727, 33913973923440109, 35233049832171443, 40360165521177913, 43952963517263700,
    40360199524577917, 34233092272492122, 39411279005766903, 45937315220586979, 43937312936293958, 40411141354456727,
    29105942580085649, 34233058269092118, 37825856255304501, 34233092272492122, 28105985020406328, 32914111574763886,
    39440147775570522, 37440145491277830, 33913973923440109, 0
  ]

abbrev PositiveTerm := Fin 6
abbrev NegativeTerm := Fin 58
def positiveArgument (term : PositiveTerm) : ℕ :=
  positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ :=
  positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ :=
  positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ :=
  negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ :=
  negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ :=
  negativeScales[term.val]?.getD 0
def positiveLogLowerNumerator (term : PositiveTerm) : ℕ :=
  positiveLogLowerNumerators[term.val]?.getD 0
def negativeLogUpperNumerator (term : NegativeTerm) : ℕ :=
  negativeLogUpperNumerators[term.val]?.getD 0

noncomputable def positiveLogLower (term : PositiveTerm) : ℝ :=
  (positiveLogLowerNumerator term : ℝ) / logBoundDenominator
noncomputable def negativeLogUpper (term : NegativeTerm) : ℝ :=
  (negativeLogUpperNumerator term : ℝ) / logBoundDenominator
def positiveLogLowerRat (term : PositiveTerm) : ℚ :=
  positiveLogLowerNumerator term / logBoundDenominator
def negativeLogUpperRat (term : NegativeTerm) : ℚ :=
  negativeLogUpperNumerator term / logBoundDenominator

theorem positiveScales_valid :
    ∀ term, 2 ^ positiveScale term ≤ positiveArgument term := by decide

theorem negativeScales_valid :
    ∀ term, 2 ^ negativeScale term ≤ negativeArgument term := by decide

noncomputable def positiveExact : ℝ :=
  Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ :=
  Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 41815323 / 1000000000000
noncomputable def negativeCeiling : ℝ := 86921073 / 500000000000

theorem positiveLogLowerRat_le_fastRat :
    ∀ term, positiveLogLowerRat term ≤
      MatrixMultiplication.RationalDyadicLog.numeratorLogLower
        (positiveArgument term) (positiveScale term) 8 := by decide +kernel

theorem negativeFastRat_le_logUpperRat :
    ∀ term, MatrixMultiplication.RationalDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpperRat term := by decide +kernel

theorem positiveLogLower_le_fast (term : PositiveTerm) :
    positiveLogLower term ≤ MatrixMultiplication.FastDyadicLog.numeratorLogLower
      (positiveArgument term) (positiveScale term) 8 := by
  simpa [positiveLogLower, positiveLogLowerRat] using
    MatrixMultiplication.RationalDyadicLog.cast_le_fastLower
      (positiveLogLowerRat_le_fastRat term)

theorem negativeFast_le_logUpper (term : NegativeTerm) :
    MatrixMultiplication.FastDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpper term := by
  simpa [negativeLogUpper, negativeLogUpperRat] using
    MatrixMultiplication.RationalDyadicLog.fastUpper_le_cast
      (negativeFastRat_le_logUpperRat term)

theorem positiveFloor_le_rationalLower : positiveFloor ≤ positiveRationalLower := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem positiveFloor_le_exact : positiveFloor ≤ positiveExact :=
  positiveFloor_le_rationalLower.trans
    (weightedLowerWithScale_le_natLogSum 8 bits
      positiveArgument positiveCoefficient positiveScale positiveLogLower
      positiveScales_valid positiveLogLower_le_fast)

theorem negativeExact_le_ceiling : negativeExact ≤ negativeCeiling :=
  (natLogSum_le_weightedUpperWithScale 8 bits
    negativeArgument negativeCoefficient negativeScale negativeLogUpper
    negativeScales_valid negativeFast_le_logUpper).trans
      negativeRationalUpper_le_ceiling

/-- Sign-separated exact form used by the directed arithmetic checker. -/
def signedForm : Form :=
  SignedDyadicLogCertificate.Form.ofSignedFamilies constantNumerator
    positiveArgument positiveCoefficient negativeArgument negativeCoefficient

/-- Exact source-order form before this shard's bounded power-of-two normalization. -/
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 9112439252613895532052480, coefficient := (-9112439252613895532052480) }, { argument := 411642769945864345585975296, coefficient := (-411642769945864345585975296) }, { argument := 411573056199586986816700416, coefficient := (-411573056199586986816700416) }, { argument := 9112439252613895532052480, coefficient := (-9112439252613895532052480) }, { argument := 650502209561755845132288, coefficient := (-650502209561755845132288) }, { argument := 22733399799690216502984704, coefficient := (-22733399799690216502984704) }, { argument := 274286448731496521932996608, coefficient := (-274286448731496521932996608) }, { argument := 22733935617707682721431552, coefficient := (-22733935617707682721431552) }, { argument := 650521345919522495791104, coefficient := (-650521345919522495791104) }, { argument := 419891711001506802292490240, coefficient := (-419891711001506802292490240) }, { argument := 18968070151401894711234920448, coefficient := (-18968070151401894711234920448) }, { argument := 18964857814573824402163499008, coefficient := (-18964857814573824402163499008) }, { argument := 419891711001506802292490240, coefficient := (-419891711001506802292490240) }, { argument := 22733399799690216502984704, coefficient := (-22733399799690216502984704) }, { argument := 794474574960673868409208832, coefficient := (-794474574960673868409208832) }, { argument := 9585614632809907676998795264, coefficient := (-9585614632809907676998795264) }, { argument := 794493300439283915361878016, coefficient := (-794493300439283915361878016) }, { argument := 22734068566783432465580032, coefficient := (-22734068566783432465580032) }, { argument := 9112439252613895532052480, coefficient := (-9112439252613895532052480) }, { argument := 419891711001506802292490240, coefficient := (-419891711001506802292490240) }, { argument := 419891046166056061024337920, coefficient := (-419891046166056061024337920) }, { argument := 9111569852409080027545600, coefficient := (-9111569852409080027545600) }, { argument := 419891046166056061024337920, coefficient := (-419891046166056061024337920) }, { argument := 18968040118312080385228406784, coefficient := (-18968040118312080385228406784) }, { argument := 18964827786570262905318539264, coefficient := (-18964827786570262905318539264) }, { argument := 419891046166056061024337920, coefficient := (-419891046166056061024337920) }, { argument := 274286448731496521932996608, coefficient := (-274286448731496521932996608) }, { argument := 9585614632809907676998795264, coefficient := (-9585614632809907676998795264) }, { argument := 115653805401246022194302025728, coefficient := (-115653805401246022194302025728) }, { argument := 9585840562282577988610424832, coefficient := (-9585840562282577988610424832) }, { argument := 274294517641234747347697664, coefficient := (-274294517641234747347697664) }, { argument := 411642769945864345585975296, coefficient := (-411642769945864345585975296) }, { argument := 18968070151401894711234920448, coefficient := (-18968070151401894711234920448) }, { argument := 18968040118312080385228406784, coefficient := (-18968040118312080385228406784) }, { argument := 411603495905337919269765120, coefficient := (-411603495905337919269765120) }, { argument := 9111569852409080027545600, coefficient := (-9111569852409080027545600) }, { argument := 411603495905337919269765120, coefficient := (-411603495905337919269765120) }, { argument := 411533788810314260173291520, coefficient := (-411533788810314260173291520) }, { argument := 9111569852409080027545600, coefficient := (-9111569852409080027545600) }, { argument := 22733935617707682721431552, coefficient := (-22733935617707682721431552) }, { argument := 794493300439283915361878016, coefficient := (-794493300439283915361878016) }, { argument := 9585840562282577988610424832, coefficient := (-9585840562282577988610424832) }, { argument := 794512026359246725796855808, coefficient := (-794512026359246725796855808) }, { argument := 22734604400563497379823616, coefficient := (-22734604400563497379823616) }, { argument := 411573056199586986816700416, coefficient := (-411573056199586986816700416) }, { argument := 18964857814573824402163499008, coefficient := (-18964857814573824402163499008) }, { argument := 18964827786570262905318539264, coefficient := (-18964827786570262905318539264) }, { argument := 411533788810314260173291520, coefficient := (-411533788810314260173291520) }, { argument := 650521345919522495791104, coefficient := (-650521345919522495791104) }, { argument := 22734068566783432465580032, coefficient := (-22734068566783432465580032) }, { argument := 274294517641234747347697664, coefficient := (-274294517641234747347697664) }, { argument := 22734604400563497379823616, coefficient := (-22734604400563497379823616) }, { argument := 650540482840239099871232, coefficient := (-650540482840239099871232) }, { argument := 9112439252613895532052480, coefficient := (-9112439252613895532052480) }, { argument := 419891711001506802292490240, coefficient := (-419891711001506802292490240) }, { argument := 419891046166056061024337920, coefficient := (-419891046166056061024337920) }, { argument := 9111569852409080027545600, coefficient := (-9111569852409080027545600) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 1682881409301358246933561344, coefficient := 1682881409301358246933561344 }, { argument := 77545422775957465435966799872, coefficient := 77545422775957465435966799872 }, { argument := 77545299994428910825191243776, coefficient := 77545299994428910825191243776 }, { argument := 1682720848840940678996295680, coefficient := 1682720848840940678996295680 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 642109615408751398996672512, coefficient := 642109615408751398996672512 }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := Form.normalizePowersOfTwo rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

/-- Sign separation retains this bounded shard's exact constant. -/
theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by
  rfl

/-- Sign separation only permutes this bounded shard's exact term list. -/
theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by
  decide +kernel

/-- Rational lower endpoint contributed by this shard. -/
noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

/-- Kernel-checked lower-bound certificate before restoring source term order. -/
noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

/-- Kernel-checked lower-bound certificate in the shard's exact source order. -/
noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard0


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-11452297358024347190762999382016)
def positiveArguments : Array ℕ := #[
    1187969, 14333263, 1187997, 16997, 90845, 8207613,
    8206223, 90845
  ]
def positiveCoefficients : Array ℕ := #[
    22440099953152678219476893696, 270747683125422478258383880192, 22440628858198759619740827648, 642128504874682877577527296, 1716013532545171677752852480, 77518713071130354722638135296,
    77505584892307977108944060416, 1716013532545171677752852480
  ]
def positiveScales : Array ℕ := #[
    20, 23, 20, 14, 16, 22,
    22, 16
  ]
def negativeArguments : Array ℕ := #[
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    316912650057057350374175801344, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    20180065758888953, 23772863743993937, 20180099762288957, 14052992510203163, 16471119491986694, 22968531275983318,
    22968286927729481, 16471119491986694
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0
  ]

abbrev PositiveTerm := Fin 8
abbrev NegativeTerm := Fin 2
def positiveArgument (term : PositiveTerm) : ℕ :=
  positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ :=
  positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ :=
  positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ :=
  negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ :=
  negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ :=
  negativeScales[term.val]?.getD 0
def positiveLogLowerNumerator (term : PositiveTerm) : ℕ :=
  positiveLogLowerNumerators[term.val]?.getD 0
def negativeLogUpperNumerator (term : NegativeTerm) : ℕ :=
  negativeLogUpperNumerators[term.val]?.getD 0

noncomputable def positiveLogLower (term : PositiveTerm) : ℝ :=
  (positiveLogLowerNumerator term : ℝ) / logBoundDenominator
noncomputable def negativeLogUpper (term : NegativeTerm) : ℝ :=
  (negativeLogUpperNumerator term : ℝ) / logBoundDenominator
def positiveLogLowerRat (term : PositiveTerm) : ℚ :=
  positiveLogLowerNumerator term / logBoundDenominator
def negativeLogUpperRat (term : NegativeTerm) : ℚ :=
  negativeLogUpperNumerator term / logBoundDenominator

theorem positiveScales_valid :
    ∀ term, 2 ^ positiveScale term ≤ positiveArgument term := by decide

theorem negativeScales_valid :
    ∀ term, 2 ^ negativeScale term ≤ negativeArgument term := by decide

noncomputable def positiveExact : ℝ :=
  Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ :=
  Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 66013411 / 500000000000
noncomputable def negativeCeiling : ℝ := 0 / 1

theorem positiveLogLowerRat_le_fastRat :
    ∀ term, positiveLogLowerRat term ≤
      MatrixMultiplication.RationalDyadicLog.numeratorLogLower
        (positiveArgument term) (positiveScale term) 8 := by decide +kernel

theorem negativeFastRat_le_logUpperRat :
    ∀ term, MatrixMultiplication.RationalDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpperRat term := by decide +kernel

theorem positiveLogLower_le_fast (term : PositiveTerm) :
    positiveLogLower term ≤ MatrixMultiplication.FastDyadicLog.numeratorLogLower
      (positiveArgument term) (positiveScale term) 8 := by
  simpa [positiveLogLower, positiveLogLowerRat] using
    MatrixMultiplication.RationalDyadicLog.cast_le_fastLower
      (positiveLogLowerRat_le_fastRat term)

theorem negativeFast_le_logUpper (term : NegativeTerm) :
    MatrixMultiplication.FastDyadicLog.numeratorLogUpper
        (negativeArgument term) (negativeScale term) 8 ≤
      negativeLogUpper term := by
  simpa [negativeLogUpper, negativeLogUpperRat] using
    MatrixMultiplication.RationalDyadicLog.fastUpper_le_cast
      (negativeFastRat_le_logUpperRat term)

theorem positiveFloor_le_rationalLower : positiveFloor ≤ positiveRationalLower := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [positiveRationalLower, negativeRationalUpper,
    positiveFloor, negativeCeiling, bits,
    positiveLogLower, negativeLogUpper, logBoundDenominator,
    positiveLogLowerNumerator, negativeLogUpperNumerator,
    positiveLogLowerNumerators, negativeLogUpperNumerators,
    positiveCoefficient, negativeCoefficient,
    positiveCoefficients, negativeCoefficients,
    Fin.sum_univ_succ, mass]

theorem positiveFloor_le_exact : positiveFloor ≤ positiveExact :=
  positiveFloor_le_rationalLower.trans
    (weightedLowerWithScale_le_natLogSum 8 bits
      positiveArgument positiveCoefficient positiveScale positiveLogLower
      positiveScales_valid positiveLogLower_le_fast)

theorem negativeExact_le_ceiling : negativeExact ≤ negativeCeiling :=
  (natLogSum_le_weightedUpperWithScale 8 bits
    negativeArgument negativeCoefficient negativeScale negativeLogUpper
    negativeScales_valid negativeFast_le_logUpper).trans
      negativeRationalUpper_le_ceiling

/-- Sign-separated exact form used by the directed arithmetic checker. -/
def signedForm : Form :=
  SignedDyadicLogCertificate.Form.ofSignedFamilies constantNumerator
    positiveArgument positiveCoefficient negativeArgument negativeCoefficient

/-- Exact source-order form before this shard's bounded power-of-two normalization. -/
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 22440099953152678219476893696, coefficient := 22440099953152678219476893696 }, { argument := 270747683125422478258383880192, coefficient := 270747683125422478258383880192 }, { argument := 22440628858198759619740827648, coefficient := 22440628858198759619740827648 }, { argument := 642128504874682877577527296, coefficient := 642128504874682877577527296 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 1716013532545171677752852480, coefficient := 1716013532545171677752852480 }, { argument := 77518713071130354722638135296, coefficient := 77518713071130354722638135296 }, { argument := 77505584892307977108944060416, coefficient := 77505584892307977108944060416 }, { argument := 1716013532545171677752852480, coefficient := 1716013532545171677752852480 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := Form.normalizePowersOfTwo rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

/-- Sign separation retains this bounded shard's exact constant. -/
theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by
  rfl

/-- Sign separation only permutes this bounded shard's exact term list. -/
theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by
  decide +kernel

/-- Rational lower endpoint contributed by this shard. -/
noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

/-- Kernel-checked lower-bound certificate before restoring source term order. -/
noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

/-- Kernel-checked lower-bound certificate in the shard's exact source order. -/
noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard1


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk6
