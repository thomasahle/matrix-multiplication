import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 22, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk22

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-50182270214854619662326180085760)
def positiveArguments : Array ℕ := #[
    441, 7, 35, 29, 521, 195,
    7, 781, 781, 559, 29, 305,
    335, 305, 335, 5, 29, 1627389869,
    1627390035, 336484643, 1222859181, 21030099
  ]
def positiveCoefficients : Array ℕ := #[
    34939619668790572878752882098176, 8665580274997661924293869568, 173311605499953238485877391360, 8975065284819006993018650624, 161241690116920780805610930176, 241398307660649153605329223680,
    8665580274997661924293869568, 241707792670470498674054004736, 241707792670470498674054004736, 173002120490131893417152610304, 8975065284819006993018650624, 188785855991020491922116444160,
    207354956580301196045603307520, 188785855991020491922116444160, 207354956580301196045603307520, 792281625142643375935439503360, 18380933703309326321702196477952, 15370262743854445336786420891648,
    15370264311680117649508631838720, 3178007600207116370534314541056, 11549578419247649751561721085952, 3177978708768974174044897148928
  ]
def positiveScales : Array ℕ := #[
    8, 2, 5, 4, 9, 7,
    2, 9, 9, 9, 4, 8,
    8, 8, 8, 2, 4, 30,
    30, 28, 30, 24
  ]
def negativeArguments : Array ℕ := #[
    85099925, 35, 29, 625356709, 195, 170198321,
    781, 781, 559, 29, 13635042347450483, 2810183345,
    13635043696050061, 2810183345, 167202297, 2810183345, 2810184015, 35,
    29, 13635043696050061, 2810184015, 13635045044650099, 2810184015, 76821825,
    195, 167200767, 2810183345, 2810184015, 781, 781,
    559, 29, 1, 5, 5, 29,
    97, 113
  ]
def negativeCoefficients : Array ℕ := #[
    1607492134058882369848554291200, 86655802749976619242938695680, 4487532642409503496509325312, 5906327124838532413669064572928, 120699153830324576802664611840, 1607477693062177754473490808832,
    120853896335235249337027002368, 120853896335235249337027002368, 86501060245065946708576305152, 4487532642409503496509325312, 3837923227197433018083178446848, 51838732965416034318701035520,
    3837923606794467827633688150016, 51838732965416034318701035520, 1579181046423231662610054119424, 51838732965416034318701035520, 51838745324734563704100618240, 86655802749976619242938695680,
    4487532642409503496509325312, 3837923606794467827633688150016, 51838745324734563704100618240, 3837923986391632115673484754944, 51838745324734563704100618240, 5804492984526038118698267443200,
    120699153830324576802664611840, 1579166595981794081495700209664, 51838732965416034318701035520, 51838745324734563704100618240, 120853896335235249337027002368, 120853896335235249337027002368,
    86501060245065946708576305152, 4487532642409503496509325312, 1267650600228229401496703205376, 792281625142643375935439503360, 792281625142643375935439503360, 18380933703309326321702196477952,
    30740527055534562986295052730368, 17905564728223740296140932775936
  ]
def negativeScales : Array ℕ := #[
    26, 5, 4, 29, 7, 27,
    9, 9, 9, 4, 53, 31,
    53, 31, 27, 31, 31, 5,
    4, 53, 31, 53, 31, 26,
    7, 27, 31, 31, 9, 9,
    9, 4, 0, 2, 2, 4,
    6, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8784634845528344, 2807354922011143, 5129283016944966, 4857980995002857, 9025139562278508, 7607330313749179,
    2807354922011143, 9609178738141526, 9609178738141526, 9126704472843189, 4857980995002857, 8252665432450248,
    8388017285345134, 8252665432450248, 8388017285345134, 2321928094887362, 4857980995002857, 30599912768606568,
    30599912915766980, 28325965421517498, 30187611133100989, 24325952305839614
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    26342654524651850, 5129283016944967, 4857980997143165, 29220104109681412, 7607330313756529, 27342641564060957,
    9609178738149255, 9609178738149255, 9126704472843191, 4857980997143165, 53598168699157628, 31388017113362478,
    53598168841850094, 31388017113362478, 27317019426181248, 31388017113362478, 31388017457327780, 5129283016944967,
    4857980997143165, 53598168841850094, 31388017457327780, 53598168984542596, 31388017457327780, 26195012901540229,
    7607330313756529, 27317006224607159, 31388017113362478, 31388017457327780, 9609178738149255, 9609178738149255,
    9126704472843191, 4857980997143165, 0, 2321928094887363, 2321928094887363, 4857980997143165,
    6599912842192769, 6820178963384638
  ]

abbrev PositiveTerm := Fin 22
abbrev NegativeTerm := Fin 38
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
noncomputable def positiveFloor : ℝ := 22531453809 / 1000000000000
noncomputable def negativeCeiling : ℝ := 21185963233 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1607492134058882369848554291200, coefficient := (-1607492134058882369848554291200) }, { argument := 86655802749976619242938695680, coefficient := (-86655802749976619242938695680) }, { argument := 4487532642409503496509325312, coefficient := (-4487532642409503496509325312) }, { argument := 5906327124838532413669064572928, coefficient := (-5906327124838532413669064572928) }, { argument := 120699153830324576802664611840, coefficient := (-120699153830324576802664611840) }, { argument := 1607477693062177754473490808832, coefficient := (-1607477693062177754473490808832) }, { argument := 120853896335235249337027002368, coefficient := (-120853896335235249337027002368) }, { argument := 120853896335235249337027002368, coefficient := (-120853896335235249337027002368) }, { argument := 86501060245065946708576305152, coefficient := (-86501060245065946708576305152) }, { argument := 4487532642409503496509325312, coefficient := (-4487532642409503496509325312) }, { argument := 3837923227197433018083178446848, coefficient := (-3837923227197433018083178446848) }, { argument := 51838732965416034318701035520, coefficient := (-51838732965416034318701035520) }, { argument := 3837923606794467827633688150016, coefficient := (-3837923606794467827633688150016) }, { argument := 51838732965416034318701035520, coefficient := (-51838732965416034318701035520) }, { argument := 1579181046423231662610054119424, coefficient := (-1579181046423231662610054119424) }, { argument := 51838732965416034318701035520, coefficient := (-51838732965416034318701035520) }, { argument := 51838745324734563704100618240, coefficient := (-51838745324734563704100618240) }, { argument := 86655802749976619242938695680, coefficient := (-86655802749976619242938695680) }, { argument := 4487532642409503496509325312, coefficient := (-4487532642409503496509325312) }, { argument := 3837923606794467827633688150016, coefficient := (-3837923606794467827633688150016) }, { argument := 51838745324734563704100618240, coefficient := (-51838745324734563704100618240) }, { argument := 3837923986391632115673484754944, coefficient := (-3837923986391632115673484754944) }, { argument := 51838745324734563704100618240, coefficient := (-51838745324734563704100618240) }, { argument := 5804492984526038118698267443200, coefficient := (-5804492984526038118698267443200) }, { argument := 120699153830324576802664611840, coefficient := (-120699153830324576802664611840) }, { argument := 1579166595981794081495700209664, coefficient := (-1579166595981794081495700209664) }, { argument := 51838732965416034318701035520, coefficient := (-51838732965416034318701035520) }, { argument := 51838745324734563704100618240, coefficient := (-51838745324734563704100618240) }, { argument := 120853896335235249337027002368, coefficient := (-120853896335235249337027002368) }, { argument := 120853896335235249337027002368, coefficient := (-120853896335235249337027002368) }, { argument := 86501060245065946708576305152, coefficient := (-86501060245065946708576305152) }, { argument := 4487532642409503496509325312, coefficient := (-4487532642409503496509325312) }, { argument := 34939619668790572878752882098176, coefficient := 34939619668790572878752882098176 }, { argument := 8665580274997661924293869568, coefficient := 8665580274997661924293869568 }, { argument := 173311605499953238485877391360, coefficient := 173311605499953238485877391360 }, { argument := 8975065284819006993018650624, coefficient := 8975065284819006993018650624 }, { argument := 161241690116920780805610930176, coefficient := 161241690116920780805610930176 }, { argument := 241398307660649153605329223680, coefficient := 241398307660649153605329223680 }, { argument := 8665580274997661924293869568, coefficient := 8665580274997661924293869568 }, { argument := 241707792670470498674054004736, coefficient := 241707792670470498674054004736 }, { argument := 241707792670470498674054004736, coefficient := 241707792670470498674054004736 }, { argument := 173002120490131893417152610304, coefficient := 173002120490131893417152610304 }, { argument := 8975065284819006993018650624, coefficient := 8975065284819006993018650624 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 188785855991020491922116444160, coefficient := 188785855991020491922116444160 }, { argument := 207354956580301196045603307520, coefficient := 207354956580301196045603307520 }, { argument := 188785855991020491922116444160, coefficient := 188785855991020491922116444160 }, { argument := 207354956580301196045603307520, coefficient := 207354956580301196045603307520 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 18380933703309326321702196477952, coefficient := 18380933703309326321702196477952 }, { argument := 18380933703309326321702196477952, coefficient := (-18380933703309326321702196477952) }, { argument := 15370262743854445336786420891648, coefficient := 15370262743854445336786420891648 }, { argument := 15370264311680117649508631838720, coefficient := 15370264311680117649508631838720 }, { argument := 30740527055534562986295052730368, coefficient := (-30740527055534562986295052730368) }, { argument := 3178007600207116370534314541056, coefficient := 3178007600207116370534314541056 }, { argument := 11549578419247649751561721085952, coefficient := 11549578419247649751561721085952 }, { argument := 3177978708768974174044897148928, coefficient := 3177978708768974174044897148928 }, { argument := 17905564728223740296140932775936, coefficient := (-17905564728223740296140932775936) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk22
