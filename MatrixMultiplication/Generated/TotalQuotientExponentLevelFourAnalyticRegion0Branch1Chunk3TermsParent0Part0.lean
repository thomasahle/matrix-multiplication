import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 3, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk3

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
def constantNumerator : ℤ := (-4908600363356526263611204567040)
def positiveArguments : Array ℕ := #[
    7, 4728177, 31415523, 9459771, 3653485, 130526175,
    32641017, 230733, 178035, 8186565, 83934051, 2046657,
    178017
  ]
def positiveCoefficients : Array ℕ := #[
    2218388550399401452619230609408, 178625476719001203980460097536, 593422451428081780850826412032, 178690022024089066291240894464, 34506190219334011487120261120, 1232784867914355626701592985600,
    1233142757180626385633758150656, 34867385142142779170935013376, 1681493033555394571240734720, 77319920331667474137722388480, 792734698427742855436531924992, 77320515349844315713019314176,
    1681323028362011264013041664
  ]
def positiveScales : Array ℕ := #[
    2, 22, 24, 23, 21, 26,
    24, 17, 17, 22, 26, 20,
    17
  ]
def negativeArguments : Array ℕ := #[
    559881982071, 25780854212973, 264620973501297, 201414471255, 559825243947, 208655994559,
    14902243081755, 29812988626305, 843208229709, 559881982071, 1866982535355, 280033566567,
    1866982535355, 85777062762525, 878841467461371, 21444430861617, 1866794042217, 14902243081755,
    532408890129345, 1065127002690825, 30116562515775, 25780854212973, 85777062762525, 12894926163771,
    280033566567, 12894926163771, 66179315604837, 6447512625135, 140002593627, 29812988626305,
    1065127002690825, 532718184800457, 7531302439161, 264620973501297, 878841467461371, 66179315604837,
    843208229709, 30116562515775, 7531302439161, 53246097945, 201414471255, 21444430861617,
    6447512625135, 559825243947, 1866794042217, 140002593627, 3, 1,
    3
  ]
def negativeCoefficients : Array ℕ := #[
    157592767864150645146648576, 7256665339177392795222540288, 74484182353428691588409720832, 7256721101528347822616739840, 157576797502019138834399232, 234925764836133160213282816,
    8389217048747046244775362560, 8391610279264252088895406080, 237342016819574249676079104, 157592767864150645146648576, 525508865658250117125242880, 157644883255296523348475904,
    525508865658250117125242880, 24144096743390202388964966400, 247371881586048145052324069376, 24144282709387671418341163008, 525455809556621448657764352, 8389217048747046244775362560,
    299719559899407185988959600640, 299806598276290797519450931200, 8477058732732783597610598400, 7256665339177392795222540288, 24144096743390202388964966400, 7259198083266141884673687552,
    157644883255296523348475904, 7259198083266141884673687552, 74511285274394591077532172288, 7259253864006138615551754240, 157628907122365044514357248, 8391610279264252088895406080,
    299806598276290797519450931200, 299893677320103146403171139584, 8479492714654996805361598464, 74484182353428691588409720832, 247371881586048145052324069376, 74511285274394591077532172288,
    237342016819574249676079104, 8477058732732783597610598400, 8479492714654996805361598464, 239799106864034932819230720, 7256721101528347822616739840, 24144282709387671418341163008,
    7259253864006138615551754240, 157576797502019138834399232, 525455809556621448657764352, 157628907122365044514357248, 950737950171172051122527404032, 2535301200456458802993406410752,
    950737950171172051122527404032
  ]
def negativeScales : Array ℕ := #[
    39, 44, 47, 37, 39, 37,
    43, 44, 39, 39, 40, 38,
    40, 46, 49, 44, 40, 43,
    48, 49, 44, 44, 46, 43,
    38, 43, 45, 42, 37, 44,
    49, 48, 42, 47, 49, 45,
    39, 44, 42, 35, 37, 44,
    42, 39, 40, 37, 1, 0,
    1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 22172852613351149, 24904974261929081, 23173373828875823, 21800841853410358, 26959763904263306,
    24960182671676804, 17815864830945358, 17441801363733830, 22964826807058068, 26322752877054781, 20964837909325821,
    17441655494530690
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    39026331796244323, 44551365299734852, 47910920745938916, 37551376385785309, 39026185586934796, 37602335412709136,
    43760594734933298, 44761006240489719, 39617097991511757, 39026331796244323, 40763845570921596, 38026808811707280,
    40763845570921596, 46285657148594158, 49642596272268185, 44285668260676417, 40763699907081362, 43760594734933298,
    48919527996075863, 49919946893058036, 44775622345088818, 44551365299734852, 46285657148594158, 43551868745829318,
    38026808811707280, 43551868745829318, 45911445610948714, 42551879831666467, 37026662597918021, 44761006240489719,
    49919946893058036, 48920365864082016, 42776036520543393, 47910920745938916, 49642596272268185, 45911445610948714,
    39617097991511757, 44775622345088818, 42776036520543393, 35631956752504038, 37551376385785309, 44285668260676417,
    42551879831666467, 39026185586934796, 40763699907081362, 37026662597918021, 1584962500724866, 0,
    1584962500724866
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
noncomputable def positiveFloor : ℝ := 1430234571 / 1000000000000
noncomputable def negativeCeiling : ℝ := 333349231 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 157592767864150645146648576, coefficient := (-157592767864150645146648576) }, { argument := 7256665339177392795222540288, coefficient := (-7256665339177392795222540288) }, { argument := 74484182353428691588409720832, coefficient := (-74484182353428691588409720832) }, { argument := 7256721101528347822616739840, coefficient := (-7256721101528347822616739840) }, { argument := 157576797502019138834399232, coefficient := (-157576797502019138834399232) }, { argument := 234925764836133160213282816, coefficient := (-234925764836133160213282816) }, { argument := 8389217048747046244775362560, coefficient := (-8389217048747046244775362560) }, { argument := 8391610279264252088895406080, coefficient := (-8391610279264252088895406080) }, { argument := 237342016819574249676079104, coefficient := (-237342016819574249676079104) }, { argument := 157592767864150645146648576, coefficient := (-157592767864150645146648576) }, { argument := 525508865658250117125242880, coefficient := (-525508865658250117125242880) }, { argument := 157644883255296523348475904, coefficient := (-157644883255296523348475904) }, { argument := 525508865658250117125242880, coefficient := (-525508865658250117125242880) }, { argument := 24144096743390202388964966400, coefficient := (-24144096743390202388964966400) }, { argument := 247371881586048145052324069376, coefficient := (-247371881586048145052324069376) }, { argument := 24144282709387671418341163008, coefficient := (-24144282709387671418341163008) }, { argument := 525455809556621448657764352, coefficient := (-525455809556621448657764352) }, { argument := 8389217048747046244775362560, coefficient := (-8389217048747046244775362560) }, { argument := 299719559899407185988959600640, coefficient := (-299719559899407185988959600640) }, { argument := 299806598276290797519450931200, coefficient := (-299806598276290797519450931200) }, { argument := 8477058732732783597610598400, coefficient := (-8477058732732783597610598400) }, { argument := 7256665339177392795222540288, coefficient := (-7256665339177392795222540288) }, { argument := 24144096743390202388964966400, coefficient := (-24144096743390202388964966400) }, { argument := 7259198083266141884673687552, coefficient := (-7259198083266141884673687552) }, { argument := 157644883255296523348475904, coefficient := (-157644883255296523348475904) }, { argument := 7259198083266141884673687552, coefficient := (-7259198083266141884673687552) }, { argument := 74511285274394591077532172288, coefficient := (-74511285274394591077532172288) }, { argument := 7259253864006138615551754240, coefficient := (-7259253864006138615551754240) }, { argument := 157628907122365044514357248, coefficient := (-157628907122365044514357248) }, { argument := 8391610279264252088895406080, coefficient := (-8391610279264252088895406080) }, { argument := 299806598276290797519450931200, coefficient := (-299806598276290797519450931200) }, { argument := 299893677320103146403171139584, coefficient := (-299893677320103146403171139584) }, { argument := 8479492714654996805361598464, coefficient := (-8479492714654996805361598464) }, { argument := 74484182353428691588409720832, coefficient := (-74484182353428691588409720832) }, { argument := 247371881586048145052324069376, coefficient := (-247371881586048145052324069376) }, { argument := 74511285274394591077532172288, coefficient := (-74511285274394591077532172288) }, { argument := 237342016819574249676079104, coefficient := (-237342016819574249676079104) }, { argument := 8477058732732783597610598400, coefficient := (-8477058732732783597610598400) }, { argument := 8479492714654996805361598464, coefficient := (-8479492714654996805361598464) }, { argument := 239799106864034932819230720, coefficient := (-239799106864034932819230720) }, { argument := 7256721101528347822616739840, coefficient := (-7256721101528347822616739840) }, { argument := 24144282709387671418341163008, coefficient := (-24144282709387671418341163008) }, { argument := 7259253864006138615551754240, coefficient := (-7259253864006138615551754240) }, { argument := 157576797502019138834399232, coefficient := (-157576797502019138834399232) }, { argument := 525455809556621448657764352, coefficient := (-525455809556621448657764352) }, { argument := 157628907122365044514357248, coefficient := (-157628907122365044514357248) }, { argument := 2218388550399401452619230609408, coefficient := 2218388550399401452619230609408 }, { argument := 178625476719001203980460097536, coefficient := 178625476719001203980460097536 }, { argument := 593422451428081780850826412032, coefficient := 593422451428081780850826412032 }, { argument := 178690022024089066291240894464, coefficient := 178690022024089066291240894464 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 34506190219334011487120261120, coefficient := 34506190219334011487120261120 }, { argument := 1232784867914355626701592985600, coefficient := 1232784867914355626701592985600 }, { argument := 1233142757180626385633758150656, coefficient := 1233142757180626385633758150656 }, { argument := 34867385142142779170935013376, coefficient := 34867385142142779170935013376 }, { argument := 2535301200456458802993406410752, coefficient := (-2535301200456458802993406410752) }, { argument := 1681493033555394571240734720, coefficient := 1681493033555394571240734720 }, { argument := 77319920331667474137722388480, coefficient := 77319920331667474137722388480 }, { argument := 792734698427742855436531924992, coefficient := 792734698427742855436531924992 }, { argument := 77320515349844315713019314176, coefficient := 77320515349844315713019314176 }, { argument := 1681323028362011264013041664, coefficient := 1681323028362011264013041664 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk3
