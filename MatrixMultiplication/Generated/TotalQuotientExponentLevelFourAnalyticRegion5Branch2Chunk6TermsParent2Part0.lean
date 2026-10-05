import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 2,
parent chunk 6, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk6

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
def constantNumerator : ℤ := (-1388765716800603865900361187328)
def positiveArguments : Array ℕ := #[
    3, 1531061, 2662239, 1533069, 201239, 16374759,
    16374727, 100617, 51985, 164479, 3510773, 1317071,
    12309
  ]
def positiveCoefficients : Array ℕ := #[
    475368975085586025561263702016, 28920924598515527482106445824, 100576545783907211232518602752, 28958854646105936472462852096, 7602594469169636265271754752, 309310452266672275159101997056,
    309309847803762467844514643968, 7602405574510321479463206912, 490984443223957012867973120, 12427681867774662001656070144, 132633253953309703486585176064, 12439383891919212982495608832,
    465020872301139703483072512
  ]
def positiveScales : Array ℕ := #[
    1, 20, 21, 20, 17, 23,
    23, 16, 15, 17, 21, 20,
    13
  ]
def negativeArguments : Array ℕ := #[
    79592206085, 251827382219, 5375207620153, 2016516042331, 18845829849, 4968002109,
    824186775965, 824184726965, 9935786973, 79592206085, 138396494415, 79696591965,
    138396494415, 437882408481, 9346516800747, 3506357781969, 32769499851, 824186775965,
    16758107304407, 16758074774541, 824166238875, 251827382219, 437882408481, 252157656051,
    79696591965, 252157656051, 5382257252337, 2019160720899, 18870546321, 824184726965,
    16758074774541, 16758042244483, 824164189995, 5375207620153, 9346516800747, 5382257252337,
    9935786973, 824166238875, 824164189995, 155243277, 2016516042331, 3506357781969,
    2019160720899, 18845829849, 32769499851, 18870546321, 1, 1,
    1
  ]
def negativeCoefficients : Array ℕ := #[
    44806428708250215535083520, 1134129704723175870115610624, 12103891517580050702683602944, 1135197612103564867269558272, 42437036142722085449367552, 44747784893736476504752128,
    1855903628559832234401464320, 1855899014622013993328312320, 44746806509235428401348608, 44806428708250215535083520, 155820600169194232699944960, 44865192734534058198958080,
    155820600169194232699944960, 3944094103334253834799153152, 42092969581056269609978560512, 3947807900075806814587846656, 147580707318081124193796096, 1855903628559832234401464320,
    75471805811562152380042575872, 75471659310069756367875342336, 1855857383144396597231616000, 1134129704723175870115610624, 3944094103334253834799153152, 1135617125829901295913271296,
    44865192734534058198958080, 1135617125829901295913271296, 12119765878018531430630424576, 1136686433780234809390399488, 42492692689766642098372608, 1855899014622013993328312320,
    75471659310069756367875342336, 75471512807712669227252973568, 1855852769476794333800693760, 12103891517580050702683602944, 42092969581056269609978560512, 12119765878018531430630424576,
    44746806509235428401348608, 1855857383144396597231616000, 1855852769476794333800693760, 44745828124734380297945088, 1135197612103564867269558272, 3947807900075806814587846656,
    1136686433780234809390399488, 42437036142722085449367552, 147580707318081124193796096, 42492692689766642098372608, 158456325028528675187087900672, 633825300114114700748351602688,
    158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    36, 37, 42, 40, 34, 32,
    39, 39, 33, 36, 37, 36,
    37, 38, 43, 41, 34, 39,
    43, 43, 39, 37, 38, 37,
    36, 37, 42, 40, 34, 39,
    43, 43, 39, 42, 43, 42,
    33, 39, 39, 27, 40, 41,
    40, 34, 34, 34, 0, 0,
    0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 20546100332661050, 21344208662977087, 20547991200252695, 17618550400127233, 23964970336932094,
    23964967517575438, 16618514554367619, 15665807780735268, 17327543872805543, 21743357286589869, 20328901689092439,
    13587425939613443
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    36211908113398363, 37873644208168517, 42289457619263051, 40875002024524171, 34133526272274816, 32210018639992964,
    39584180359600001, 39584176772930208, 33209987095953360, 36211908113398363, 37010016443714327, 36213798980990013,
    37010016443714327, 38671752535819337, 43087565949579015, 41673110352107477, 34931634610209587, 39584180359600001,
    43929924458183674, 43929921657704655, 39584144410070216, 37873644208168517, 38671752535819337, 37875535075856362,
    36213798980990013, 37875535075856362, 42291348486854701, 40876892892214293, 34135417139866466, 39584176772930208,
    43929921657704655, 43929918857203670, 39584140823521107, 42289457619263051, 43087565949579015, 42291348486854701,
    33209987095953360, 39584144410070216, 39584140823521107, 27209955551224041, 40875002024524171, 41673110352107477,
    40876892892214293, 34133526272274816, 34931634610209587, 34135417139866466, 0, 0,
    0
  ]

abbrev PositiveTerm := Fin 13
abbrev NegativeTerm := Fin 49
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
noncomputable def positiveFloor : ℝ := 271328061 / 1000000000000
noncomputable def negativeCeiling : ℝ := 61862381 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 44806428708250215535083520, coefficient := (-44806428708250215535083520) }, { argument := 1134129704723175870115610624, coefficient := (-1134129704723175870115610624) }, { argument := 12103891517580050702683602944, coefficient := (-12103891517580050702683602944) }, { argument := 1135197612103564867269558272, coefficient := (-1135197612103564867269558272) }, { argument := 42437036142722085449367552, coefficient := (-42437036142722085449367552) }, { argument := 44747784893736476504752128, coefficient := (-44747784893736476504752128) }, { argument := 1855903628559832234401464320, coefficient := (-1855903628559832234401464320) }, { argument := 1855899014622013993328312320, coefficient := (-1855899014622013993328312320) }, { argument := 44746806509235428401348608, coefficient := (-44746806509235428401348608) }, { argument := 44806428708250215535083520, coefficient := (-44806428708250215535083520) }, { argument := 155820600169194232699944960, coefficient := (-155820600169194232699944960) }, { argument := 44865192734534058198958080, coefficient := (-44865192734534058198958080) }, { argument := 155820600169194232699944960, coefficient := (-155820600169194232699944960) }, { argument := 3944094103334253834799153152, coefficient := (-3944094103334253834799153152) }, { argument := 42092969581056269609978560512, coefficient := (-42092969581056269609978560512) }, { argument := 3947807900075806814587846656, coefficient := (-3947807900075806814587846656) }, { argument := 147580707318081124193796096, coefficient := (-147580707318081124193796096) }, { argument := 1855903628559832234401464320, coefficient := (-1855903628559832234401464320) }, { argument := 75471805811562152380042575872, coefficient := (-75471805811562152380042575872) }, { argument := 75471659310069756367875342336, coefficient := (-75471659310069756367875342336) }, { argument := 1855857383144396597231616000, coefficient := (-1855857383144396597231616000) }, { argument := 1134129704723175870115610624, coefficient := (-1134129704723175870115610624) }, { argument := 3944094103334253834799153152, coefficient := (-3944094103334253834799153152) }, { argument := 1135617125829901295913271296, coefficient := (-1135617125829901295913271296) }, { argument := 44865192734534058198958080, coefficient := (-44865192734534058198958080) }, { argument := 1135617125829901295913271296, coefficient := (-1135617125829901295913271296) }, { argument := 12119765878018531430630424576, coefficient := (-12119765878018531430630424576) }, { argument := 1136686433780234809390399488, coefficient := (-1136686433780234809390399488) }, { argument := 42492692689766642098372608, coefficient := (-42492692689766642098372608) }, { argument := 1855899014622013993328312320, coefficient := (-1855899014622013993328312320) }, { argument := 75471659310069756367875342336, coefficient := (-75471659310069756367875342336) }, { argument := 75471512807712669227252973568, coefficient := (-75471512807712669227252973568) }, { argument := 1855852769476794333800693760, coefficient := (-1855852769476794333800693760) }, { argument := 12103891517580050702683602944, coefficient := (-12103891517580050702683602944) }, { argument := 42092969581056269609978560512, coefficient := (-42092969581056269609978560512) }, { argument := 12119765878018531430630424576, coefficient := (-12119765878018531430630424576) }, { argument := 44746806509235428401348608, coefficient := (-44746806509235428401348608) }, { argument := 1855857383144396597231616000, coefficient := (-1855857383144396597231616000) }, { argument := 1855852769476794333800693760, coefficient := (-1855852769476794333800693760) }, { argument := 44745828124734380297945088, coefficient := (-44745828124734380297945088) }, { argument := 1135197612103564867269558272, coefficient := (-1135197612103564867269558272) }, { argument := 3947807900075806814587846656, coefficient := (-3947807900075806814587846656) }, { argument := 1136686433780234809390399488, coefficient := (-1136686433780234809390399488) }, { argument := 42437036142722085449367552, coefficient := (-42437036142722085449367552) }, { argument := 147580707318081124193796096, coefficient := (-147580707318081124193796096) }, { argument := 42492692689766642098372608, coefficient := (-42492692689766642098372608) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 28920924598515527482106445824, coefficient := 28920924598515527482106445824 }, { argument := 100576545783907211232518602752, coefficient := 100576545783907211232518602752 }, { argument := 28958854646105936472462852096, coefficient := 28958854646105936472462852096 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 7602594469169636265271754752, coefficient := 7602594469169636265271754752 }, { argument := 309310452266672275159101997056, coefficient := 309310452266672275159101997056 }, { argument := 309309847803762467844514643968, coefficient := 309309847803762467844514643968 }, { argument := 7602405574510321479463206912, coefficient := 7602405574510321479463206912 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 490984443223957012867973120, coefficient := 490984443223957012867973120 }, { argument := 12427681867774662001656070144, coefficient := 12427681867774662001656070144 }, { argument := 132633253953309703486585176064, coefficient := 132633253953309703486585176064 }, { argument := 12439383891919212982495608832, coefficient := 12439383891919212982495608832 }, { argument := 465020872301139703483072512, coefficient := 465020872301139703483072512 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch2.Chunk6
