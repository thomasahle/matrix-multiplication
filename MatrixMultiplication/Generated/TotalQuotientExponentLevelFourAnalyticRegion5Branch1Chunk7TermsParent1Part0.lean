import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 7, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk7

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
def constantNumerator : ℤ := (-933888101551493986393201311744)
def positiveArguments : Array ℕ := #[
    3, 3022201, 5368415, 3018185, 467059, 2038767,
    8155085, 467067, 6015, 1318507, 14043967, 1322055,
    44567
  ]
def positiveCoefficients : Array ℕ := #[
    475368975085586025561263702016, 28543881413790249268954529792, 101406492248538585639535247360, 28505951366199840278598123520, 8822495068490454495454560256, 308089758309782334828523290624,
    308090400551624005100272353280, 8822646184217906324101398528, 454480550311374655366103040, 12452946528458014603549343744, 132641518094654725365709144064, 12486456441020457605985730560,
    420923414084102956477579264
  ]
def positiveScales : Array ℕ := #[
    1, 21, 22, 21, 18, 20,
    22, 18, 12, 20, 23, 20,
    15
  ]
def negativeArguments : Array ℕ := #[
    18178539015, 3984793173907, 42443691111367, 3995515943055, 134690431967, 13588831641,
    476157418369, 952316855345, 27178076571, 18178539015, 32291016225, 18154382775,
    32291016225, 7078292756405, 75393843102305, 7097339892825, 239254151305, 476157418369,
    129892486999, 8313136489053, 476165600325, 3984793173907, 7078292756405, 3979498049795,
    18154382775, 3979498049795, 42387290539895, 3990206570175, 134511450895, 952316855345,
    8313136489053, 8313153810203, 952333219311, 42443691111367, 75393843102305, 42387290539895,
    27178076571, 476165600325, 952333219311, 6794622459, 3995515943055, 7097339892825,
    3990206570175, 134690431967, 239254151305, 134511450895, 1, 1,
    1
  ]
def negativeCoefficients : Array ℕ := #[
    40934430767047011697950720, 1121619565822253829028052992, 11946836967086303402631626752, 1124637757018460869707694080, 37911986201059521411940352, 61198657114808005674663936,
    2144422371936325767239041024, 2144426917435192270976450560, 61199587758901203837124608, 40934430767047011697950720, 145425808638324640422297600, 40880035750315675562803200,
    145425808638324640422297600, 3984724577520604876751503360, 42442960462696304766783324160, 3995447162081053252150886400, 134688113333005283659612160, 2144422371936325767239041024,
    74877920774006194718231232512, 74878076788758328399758360576, 2144459220190318529033011200, 1121619565822253829028052992, 3984724577520604876751503360, 1120129120886148595995115520,
    40880035750315675562803200, 1120129120886148595995115520, 11930961617544754513439621120, 1123143301410714681134284800, 37861607507986673167237120, 2144426917435192270976450560,
    74878076788758328399758360576, 74878232803807699656691941376, 2144463765810782222709424128, 11946836967086303402631626752, 42442960462696304766783324160, 11930961617544754513439621120,
    61199587758901203837124608, 2144459220190318529033011200, 2144463765810782222709424128, 61200518348951206471139328, 1124637757018460869707694080, 3995447162081053252150886400,
    1123143301410714681134284800, 37911986201059521411940352, 134688113333005283659612160, 37861607507986673167237120, 158456325028528675187087900672, 633825300114114700748351602688,
    158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    34, 41, 45, 41, 36, 33,
    38, 39, 34, 34, 34, 34,
    34, 42, 46, 42, 37, 38,
    36, 42, 38, 41, 42, 41,
    34, 41, 45, 41, 36, 39,
    42, 42, 39, 45, 46, 45,
    34, 38, 39, 32, 41, 42,
    41, 36, 37, 36, 0, 0,
    0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 21527168183519786, 22356064771283228, 21525249808059045, 18833245280463232, 20959265475289420,
    22959268482718643, 18833269991391543, 12554349022063343, 20330473799865652, 23743447175542703, 20334350766273187,
    15443688229645390
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    34081517205583267, 41857641985388201, 45270615359074613, 41861518951947626, 36970856427927148, 33661702368348530,
    38792647653890339, 39792650711945452, 34661724307153625, 34081517205583267, 34910413798604582, 34079598830122524,
    34910413798604582, 42686538571201449, 46099511946838014, 42690415537614098, 37799753001571410, 38792647653890339,
    36918527037327328, 42918530043306879, 38792672443940038, 41857641985388201, 42686538571201449, 41855723609856051,
    34079598830122524, 41855723609856051, 45268696983613869, 41859600576410431, 36968938052006461, 39792650711945452,
    42918530043306879, 42918533049285894, 39792675502024409, 45270615359074613, 46099511946838014, 45268696983613869,
    34661724307153625, 38792672443940038, 39792675502024409, 32661746244351131, 41861518951947626, 42690415537614098,
    41859600576410431, 36970856427927148, 37799753001571410, 36968938052006461, 0, 0,
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
noncomputable def positiveFloor : ℝ := 3277149 / 12500000000
noncomputable def negativeCeiling : ℝ := 60942193 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 40934430767047011697950720, coefficient := (-40934430767047011697950720) }, { argument := 1121619565822253829028052992, coefficient := (-1121619565822253829028052992) }, { argument := 11946836967086303402631626752, coefficient := (-11946836967086303402631626752) }, { argument := 1124637757018460869707694080, coefficient := (-1124637757018460869707694080) }, { argument := 37911986201059521411940352, coefficient := (-37911986201059521411940352) }, { argument := 61198657114808005674663936, coefficient := (-61198657114808005674663936) }, { argument := 2144422371936325767239041024, coefficient := (-2144422371936325767239041024) }, { argument := 2144426917435192270976450560, coefficient := (-2144426917435192270976450560) }, { argument := 61199587758901203837124608, coefficient := (-61199587758901203837124608) }, { argument := 40934430767047011697950720, coefficient := (-40934430767047011697950720) }, { argument := 145425808638324640422297600, coefficient := (-145425808638324640422297600) }, { argument := 40880035750315675562803200, coefficient := (-40880035750315675562803200) }, { argument := 145425808638324640422297600, coefficient := (-145425808638324640422297600) }, { argument := 3984724577520604876751503360, coefficient := (-3984724577520604876751503360) }, { argument := 42442960462696304766783324160, coefficient := (-42442960462696304766783324160) }, { argument := 3995447162081053252150886400, coefficient := (-3995447162081053252150886400) }, { argument := 134688113333005283659612160, coefficient := (-134688113333005283659612160) }, { argument := 2144422371936325767239041024, coefficient := (-2144422371936325767239041024) }, { argument := 74877920774006194718231232512, coefficient := (-74877920774006194718231232512) }, { argument := 74878076788758328399758360576, coefficient := (-74878076788758328399758360576) }, { argument := 2144459220190318529033011200, coefficient := (-2144459220190318529033011200) }, { argument := 1121619565822253829028052992, coefficient := (-1121619565822253829028052992) }, { argument := 3984724577520604876751503360, coefficient := (-3984724577520604876751503360) }, { argument := 1120129120886148595995115520, coefficient := (-1120129120886148595995115520) }, { argument := 40880035750315675562803200, coefficient := (-40880035750315675562803200) }, { argument := 1120129120886148595995115520, coefficient := (-1120129120886148595995115520) }, { argument := 11930961617544754513439621120, coefficient := (-11930961617544754513439621120) }, { argument := 1123143301410714681134284800, coefficient := (-1123143301410714681134284800) }, { argument := 37861607507986673167237120, coefficient := (-37861607507986673167237120) }, { argument := 2144426917435192270976450560, coefficient := (-2144426917435192270976450560) }, { argument := 74878076788758328399758360576, coefficient := (-74878076788758328399758360576) }, { argument := 74878232803807699656691941376, coefficient := (-74878232803807699656691941376) }, { argument := 2144463765810782222709424128, coefficient := (-2144463765810782222709424128) }, { argument := 11946836967086303402631626752, coefficient := (-11946836967086303402631626752) }, { argument := 42442960462696304766783324160, coefficient := (-42442960462696304766783324160) }, { argument := 11930961617544754513439621120, coefficient := (-11930961617544754513439621120) }, { argument := 61199587758901203837124608, coefficient := (-61199587758901203837124608) }, { argument := 2144459220190318529033011200, coefficient := (-2144459220190318529033011200) }, { argument := 2144463765810782222709424128, coefficient := (-2144463765810782222709424128) }, { argument := 61200518348951206471139328, coefficient := (-61200518348951206471139328) }, { argument := 1124637757018460869707694080, coefficient := (-1124637757018460869707694080) }, { argument := 3995447162081053252150886400, coefficient := (-3995447162081053252150886400) }, { argument := 1123143301410714681134284800, coefficient := (-1123143301410714681134284800) }, { argument := 37911986201059521411940352, coefficient := (-37911986201059521411940352) }, { argument := 134688113333005283659612160, coefficient := (-134688113333005283659612160) }, { argument := 37861607507986673167237120, coefficient := (-37861607507986673167237120) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 28543881413790249268954529792, coefficient := 28543881413790249268954529792 }, { argument := 101406492248538585639535247360, coefficient := 101406492248538585639535247360 }, { argument := 28505951366199840278598123520, coefficient := 28505951366199840278598123520 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 8822495068490454495454560256, coefficient := 8822495068490454495454560256 }, { argument := 308089758309782334828523290624, coefficient := 308089758309782334828523290624 }, { argument := 308090400551624005100272353280, coefficient := 308090400551624005100272353280 }, { argument := 8822646184217906324101398528, coefficient := 8822646184217906324101398528 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 454480550311374655366103040, coefficient := 454480550311374655366103040 }, { argument := 12452946528458014603549343744, coefficient := 12452946528458014603549343744 }, { argument := 132641518094654725365709144064, coefficient := 132641518094654725365709144064 }, { argument := 12486456441020457605985730560, coefficient := 12486456441020457605985730560 }, { argument := 420923414084102956477579264, coefficient := 420923414084102956477579264 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk7
