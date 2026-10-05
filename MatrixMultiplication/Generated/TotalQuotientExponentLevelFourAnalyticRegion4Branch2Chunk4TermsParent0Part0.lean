import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 4, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk4

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
def constantNumerator : ℤ := 1445141832820199652401243750400
def positiveArguments : Array ℕ := #[
    13, 12582907, 12582917, 2659633, 37431923, 10649801,
    570413, 24595393, 1537213, 285217
  ]
def positiveCoefficients : Array ℕ := #[
    1029966112685436388716071354368, 237684393095463355387727577088, 237684581990122670173536124928, 200956187774944689738206937088, 707069034258229514705548869632, 201169053166526521865859497984,
    5387398465186245870559952896, 232296919072413383602844205056, 232297060743407869692200615936, 5387596804578526395658928128
  ]
def positiveScales : Array ℕ := #[
    3, 23, 23, 21, 25, 23,
    19, 24, 20, 18
  ]
def negativeArguments : Array ℕ := #[
    2392485017737, 103160513808297, 12895072090359, 1196286549003, 64675133147885, 227551017274007,
    16185937037983, 2392485017737, 2392486037367, 2392486037367, 103160596674647, 12895082448649,
    1196287058933, 227551017274007, 400332031808929, 227791834040871, 103160513808297, 103160596674647,
    16185937037983, 227791834040871, 64812441275229, 12895072090359, 12895082448649, 1196286549003,
    1196287058933, 3, 7, 3
  ]
def negativeCoefficients : Array ℕ := #[
    1346849329296230964153810944, 58074206443299409553642225664, 58074241861056475325282648064, 1346898914079561850785103872, 18204431596559506248103362560, 64049917287687201480708718592,
    18223745003225637140291387392, 1346849329296230964153810944, 1346849903296891971126165504, 1346849903296891971126165504, 58074253092907282247779876864, 58074288510647459520817659904,
    1346899488209701347044360192, 64049917287687201480708718592, 225366898659895774515820494848, 64117701181531781356245221376, 58074206443299409553642225664, 58074253092907282247779876864,
    18223745003225637140291387392, 64117701181531781356245221376, 18243080398505842436393140224, 58074241861056475325282648064, 58074288510647459520817659904, 1346898914079561850785103872,
    1346899488209701347044360192, 475368975085586025561263702016, 1109194275199700726309615304704, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    41, 46, 43, 40, 45, 47,
    43, 41, 41, 41, 46, 43,
    40, 47, 48, 47, 46, 46,
    43, 47, 45, 43, 43, 40,
    40, 1, 2, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3700439718136550, 23584961927445308, 23584963073996313, 21342795752791702, 25157765830304070, 23344323137010496,
    19121647336341003, 24551884771706975, 20551885651563582, 18121700448801941
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    41121647028916929, 46551884192267542, 43551885072124711, 40121700141319841, 45878276355494756, 47693183364418933,
    43879806125181939, 41121647028916929, 41121647643765014, 41121647643765014, 46551885351149170, 43551886231005213,
    40121700756283978, 47693183364418933, 48508190383277172, 47694709358237542, 46551884192267542, 46551885351149170,
    43879806125181939, 47694709358237542, 45881336013389308, 43551885072124711, 43551886231005213, 40121700141319841,
    40121700756283978, 1584962500724866, 2807354922807594, 1584962500724866
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 28
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
noncomputable def positiveFloor : ℝ := 631637669 / 1000000000000
noncomputable def negativeCeiling : ℝ := 63096609 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1346849329296230964153810944, coefficient := (-1346849329296230964153810944) }, { argument := 58074206443299409553642225664, coefficient := (-58074206443299409553642225664) }, { argument := 58074241861056475325282648064, coefficient := (-58074241861056475325282648064) }, { argument := 1346898914079561850785103872, coefficient := (-1346898914079561850785103872) }, { argument := 18204431596559506248103362560, coefficient := (-18204431596559506248103362560) }, { argument := 64049917287687201480708718592, coefficient := (-64049917287687201480708718592) }, { argument := 18223745003225637140291387392, coefficient := (-18223745003225637140291387392) }, { argument := 1346849329296230964153810944, coefficient := (-1346849329296230964153810944) }, { argument := 1346849903296891971126165504, coefficient := (-1346849903296891971126165504) }, { argument := 1346849903296891971126165504, coefficient := (-1346849903296891971126165504) }, { argument := 58074253092907282247779876864, coefficient := (-58074253092907282247779876864) }, { argument := 58074288510647459520817659904, coefficient := (-58074288510647459520817659904) }, { argument := 1346899488209701347044360192, coefficient := (-1346899488209701347044360192) }, { argument := 64049917287687201480708718592, coefficient := (-64049917287687201480708718592) }, { argument := 225366898659895774515820494848, coefficient := (-225366898659895774515820494848) }, { argument := 64117701181531781356245221376, coefficient := (-64117701181531781356245221376) }, { argument := 58074206443299409553642225664, coefficient := (-58074206443299409553642225664) }, { argument := 58074253092907282247779876864, coefficient := (-58074253092907282247779876864) }, { argument := 18223745003225637140291387392, coefficient := (-18223745003225637140291387392) }, { argument := 64117701181531781356245221376, coefficient := (-64117701181531781356245221376) }, { argument := 18243080398505842436393140224, coefficient := (-18243080398505842436393140224) }, { argument := 58074241861056475325282648064, coefficient := (-58074241861056475325282648064) }, { argument := 58074288510647459520817659904, coefficient := (-58074288510647459520817659904) }, { argument := 1346898914079561850785103872, coefficient := (-1346898914079561850785103872) }, { argument := 1346899488209701347044360192, coefficient := (-1346899488209701347044360192) }, { argument := 1029966112685436388716071354368, coefficient := 1029966112685436388716071354368 }, { argument := 237684393095463355387727577088, coefficient := 237684393095463355387727577088 }, { argument := 237684581990122670173536124928, coefficient := 237684581990122670173536124928 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 200956187774944689738206937088, coefficient := 200956187774944689738206937088 }, { argument := 707069034258229514705548869632, coefficient := 707069034258229514705548869632 }, { argument := 201169053166526521865859497984, coefficient := 201169053166526521865859497984 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 5387398465186245870559952896, coefficient := 5387398465186245870559952896 }, { argument := 232296919072413383602844205056, coefficient := 232296919072413383602844205056 }, { argument := 232297060743407869692200615936, coefficient := 232297060743407869692200615936 }, { argument := 5387596804578526395658928128, coefficient := 5387596804578526395658928128 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk4
