import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 0, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk0

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 158456325028528675187087900672
def positiveArguments : Array ℕ := #[
    1, 39217, 151941, 222933, 1215537, 19611,
    173345, 4107623, 8213055, 87785
  ]
def positiveCoefficients : Array ℕ := #[
    158456325028528675187087900672, 370394092717397752691032064, 11480337372379148214626942976, 134754729872074062902385967104, 11480422374975839868240789504, 370441316382226449143169024,
    1637197235946077299136266240, 77590804717857842726470418432, 77570111307929907941144002560, 1658211766794847220337213440
  ]
def positiveScales : Array ℕ := #[
    0, 15, 17, 17, 20, 14,
    17, 21, 22, 16
  ]
def negativeArguments : Array ℕ := #[
    6798070865, 161088651191, 322091377935, 3442664345, 26338212645, 624116346243,
    1247899789755, 13338140685, 6798070865, 26338212645, 38644320885, 210707261265,
    3399468795, 38644320885, 915724718259, 1830960990315, 19570173405, 161088651191,
    624116346243, 915724718259, 4992967738551, 80554594653, 210707261265, 4992967738551,
    9983272235535, 106705915545, 322091377935, 1247899789755, 1830960990315, 9983272235535,
    161066221605, 3399468795, 80554594653, 161066221605, 1721551635, 3442664345,
    13338140685, 19570173405, 106705915545, 1721551635, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1913486838403264088637440, 90684848684675425833582592, 90660663102957224837775360, 1938047732662961585520640, 59308382326813442923560960, 2810770144375810261178646528,
    2810020514068169150945034240, 60069645418781252266229760, 1913486838403264088637440, 59308382326813442923560960, 696154196550687504822435840, 59308821457331984101539840,
    1913730799802453631959040, 696154196550687504822435840, 32992459999401478676872691712, 32983660934850193342290984960, 705089805234671927206871040, 90684848684675425833582592,
    2810770144375810261178646528, 32992459999401478676872691712, 2810790955851398961967398912, 90696410615558037382889472, 59308821457331984101539840, 2810790955851398961967398912,
    2810041319993352785976360960, 60070090185836202075095040, 90660663102957224837775360, 2810020514068169150945034240, 32983660934850193342290984960, 2810041319993352785976360960,
    90672221950281466521845760, 1913730799802453631959040, 90696410615558037382889472, 90672221950281466521845760, 1938294825471267034890240, 1938047732662961585520640,
    60069645418781252266229760, 705089805234671927206871040, 60070090185836202075095040, 1938294825471267034890240, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    32, 37, 38, 31, 34, 39,
    40, 33, 32, 34, 35, 37,
    31, 35, 39, 40, 34, 37,
    39, 39, 42, 36, 37, 42,
    43, 36, 38, 40, 40, 43,
    37, 31, 36, 37, 30, 31,
    33, 34, 36, 30, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 15259191556827033, 17213151695924778, 17766250663973315, 20213162377873116, 14259375482558218,
    17403286698175498, 21969872344780066, 22969487527773511, 16421686824157693
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    32662478255031708, 37229063902503228, 38228679085491009, 31680878381030589, 34616438394109133, 39183024041600972,
    40182639224588753, 33634838520096891, 32662478255031708, 34616438394109133, 35169537362168624, 37616449076057473,
    31662662180763028, 35169537362168624, 39736123009834865, 40735738192821231, 34187937488150820, 37229063902503228,
    39183024041600972, 39736123009834865, 42183034723549310, 36229247828234413, 37616449076057473, 42183034723549310,
    43182649906537091, 36634849202045233, 38228679085491009, 40182639224588753, 40735738192821231, 43182649906537091,
    37228863011222194, 31662662180763028, 36229247828234413, 37228863011222194, 30681062306761978, 31680878381030589,
    33634838520096891, 34187937488150820, 36634849202045233, 30681062306761978, 0, 0
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 42
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
noncomputable def positiveFloor : ℝ := 76758153 / 1000000000000
noncomputable def negativeCeiling : ℝ := 38379077 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1913486838403264088637440, coefficient := (-1913486838403264088637440) }, { argument := 90684848684675425833582592, coefficient := (-90684848684675425833582592) }, { argument := 90660663102957224837775360, coefficient := (-90660663102957224837775360) }, { argument := 1938047732662961585520640, coefficient := (-1938047732662961585520640) }, { argument := 59308382326813442923560960, coefficient := (-59308382326813442923560960) }, { argument := 2810770144375810261178646528, coefficient := (-2810770144375810261178646528) }, { argument := 2810020514068169150945034240, coefficient := (-2810020514068169150945034240) }, { argument := 60069645418781252266229760, coefficient := (-60069645418781252266229760) }, { argument := 1913486838403264088637440, coefficient := (-1913486838403264088637440) }, { argument := 59308382326813442923560960, coefficient := (-59308382326813442923560960) }, { argument := 696154196550687504822435840, coefficient := (-696154196550687504822435840) }, { argument := 59308821457331984101539840, coefficient := (-59308821457331984101539840) }, { argument := 1913730799802453631959040, coefficient := (-1913730799802453631959040) }, { argument := 696154196550687504822435840, coefficient := (-696154196550687504822435840) }, { argument := 32992459999401478676872691712, coefficient := (-32992459999401478676872691712) }, { argument := 32983660934850193342290984960, coefficient := (-32983660934850193342290984960) }, { argument := 705089805234671927206871040, coefficient := (-705089805234671927206871040) }, { argument := 90684848684675425833582592, coefficient := (-90684848684675425833582592) }, { argument := 2810770144375810261178646528, coefficient := (-2810770144375810261178646528) }, { argument := 32992459999401478676872691712, coefficient := (-32992459999401478676872691712) }, { argument := 2810790955851398961967398912, coefficient := (-2810790955851398961967398912) }, { argument := 90696410615558037382889472, coefficient := (-90696410615558037382889472) }, { argument := 59308821457331984101539840, coefficient := (-59308821457331984101539840) }, { argument := 2810790955851398961967398912, coefficient := (-2810790955851398961967398912) }, { argument := 2810041319993352785976360960, coefficient := (-2810041319993352785976360960) }, { argument := 60070090185836202075095040, coefficient := (-60070090185836202075095040) }, { argument := 90660663102957224837775360, coefficient := (-90660663102957224837775360) }, { argument := 2810020514068169150945034240, coefficient := (-2810020514068169150945034240) }, { argument := 32983660934850193342290984960, coefficient := (-32983660934850193342290984960) }, { argument := 2810041319993352785976360960, coefficient := (-2810041319993352785976360960) }, { argument := 90672221950281466521845760, coefficient := (-90672221950281466521845760) }, { argument := 1913730799802453631959040, coefficient := (-1913730799802453631959040) }, { argument := 90696410615558037382889472, coefficient := (-90696410615558037382889472) }, { argument := 90672221950281466521845760, coefficient := (-90672221950281466521845760) }, { argument := 1938294825471267034890240, coefficient := (-1938294825471267034890240) }, { argument := 1938047732662961585520640, coefficient := (-1938047732662961585520640) }, { argument := 60069645418781252266229760, coefficient := (-60069645418781252266229760) }, { argument := 705089805234671927206871040, coefficient := (-705089805234671927206871040) }, { argument := 60070090185836202075095040, coefficient := (-60070090185836202075095040) }, { argument := 1938294825471267034890240, coefficient := (-1938294825471267034890240) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 370394092717397752691032064, coefficient := 370394092717397752691032064 }, { argument := 11480337372379148214626942976, coefficient := 11480337372379148214626942976 }, { argument := 134754729872074062902385967104, coefficient := 134754729872074062902385967104 }, { argument := 11480422374975839868240789504, coefficient := 11480422374975839868240789504 }, { argument := 370441316382226449143169024, coefficient := 370441316382226449143169024 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1637197235946077299136266240, coefficient := 1637197235946077299136266240 }, { argument := 77590804717857842726470418432, coefficient := 77590804717857842726470418432 }, { argument := 77570111307929907941144002560, coefficient := 77570111307929907941144002560 }, { argument := 1658211766794847220337213440, coefficient := 1658211766794847220337213440 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk0
