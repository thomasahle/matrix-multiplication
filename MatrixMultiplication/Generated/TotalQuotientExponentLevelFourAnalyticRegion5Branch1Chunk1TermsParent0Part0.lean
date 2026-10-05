import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 1, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk1

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
def constantNumerator : ℤ := 2021258163127219778713905266688
def positiveArguments : Array ℕ := #[
    3, 3103105, 10567955, 776539, 51013, 31971,
    8184503, 204085, 38201, 1276761, 7073665, 638373,
    19089
  ]
def positiveCoefficients : Array ℕ := #[
    475368975085586025561263702016, 29307998089650420821692252160, 99811512968949362968609423360, 29336813969928891396786225152, 7708866604500134761160769536, 309204539031194474756249223168,
    309201781169168478883444424704, 7710113309251612347497185280, 360798244024206633616801792, 12058666706070262185367437312, 133617754028192435642155663360, 12058525035075776096011026432,
    360581015165994629936971776
  ]
def positiveScales : Array ℕ := #[
    1, 21, 23, 19, 15, 14,
    22, 17, 15, 20, 22, 19,
    14
  ]
def negativeArguments : Array ℕ := #[
    118541714105, 3961923442905, 21950325229825, 1980938448165, 59235171345, 40993226575,
    1670723297097, 1670707386221, 41000569339, 118541714105, 403706448955, 29664566339,
    403706448955, 13492752793755, 74754173405075, 6746297137215, 201731692995, 1670723297097,
    66986639901551, 66986043442903, 1670992778865, 3961923442905, 13492752793755, 991454710179,
    29664566339, 991454710179, 5492976745435, 495721531047, 14823352971, 1670707386221,
    66986043442903, 4186590436749, 417744216635, 21950325229825, 74754173405075, 5492976745435,
    41000569339, 1670992778865, 417744216635, 5125989077, 1980938448165, 6746297137215,
    495721531047, 59235171345, 201731692995, 14823352971, 1, 1,
    1
  ]
def negativeCoefficients : Array ℕ := #[
    33366526216946116859002880, 1115182308821086911521095680, 12356934565712633371453030400, 1115169207124972825718292480, 33346436949571185294704640, 46154269981971078499532800,
    1881067204561313920375062528, 1881049290507507735833083904, 46162537199274645872705536, 33366526216946116859002880, 113633263317550260268564480, 33399332477606939680833536,
    113633263317550260268564480, 3797872278384827304278753280, 42082858436435651517113958400, 3797827659161514740369326080, 113564847175137662274109440, 1881067204561313920375062528,
    75420251624856670614610509824, 75419580072120451937150697472, 1881370614058800905988341760, 1115182308821086911521095680, 3797872278384827304278753280, 1116278765829216876883869696,
    33399332477606939680833536, 1116278765829216876883869696, 12369084011947932932510842880, 1116265651251400481917894656, 33379223458288467399671808, 1881049290507507735833083904,
    75419580072120451937150697472, 75418908523582714012307030016, 1881352698373565756431400960, 12356934565712633371453030400, 42082858436435651517113958400, 12369084011947932932510842880,
    46162537199274645872705536, 1881370614058800905988341760, 1881352698373565756431400960, 46170804994164865456144384, 1115169207124972825718292480, 3797827659161514740369326080,
    1116265651251400481917894656, 33346436949571185294704640, 113564847175137662274109440, 33379223458288467399671808, 158456325028528675187087900672, 633825300114114700748351602688,
    158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    36, 41, 44, 40, 35, 35,
    40, 40, 35, 36, 38, 34,
    38, 43, 46, 42, 37, 40,
    45, 45, 40, 41, 43, 39,
    34, 39, 42, 38, 33, 40,
    45, 41, 38, 44, 46, 42,
    35, 40, 38, 32, 40, 42,
    38, 35, 37, 33, 0, 0,
    0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 21565281083598471, 23333192892701584, 19566698857122238, 15638577325565731, 14964476248668600,
    22964463380902912, 17638810624367123, 15221322784202037, 20284057058041302, 22754026465718032, 19284040108469115,
    14220453906972867
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    36786603868291050, 41849338143350275, 44319307549331863, 40849321193777534, 35785734991053106, 35254666497776561,
    40603609954662052, 40603596215312605, 35254924892186027, 36786603868291050, 38554515676905147, 34788021641829458,
    38554515676905147, 43617249950751939, 46087219358434844, 42617233001179747, 37553646799675937, 40603609954662052,
    45928938627874341, 45928925781851997, 40603842637512645, 41849338143350275, 43617249950751939, 39850755916920963,
    34788021641829458, 39850755916920963, 42320725322855635, 38850738967348208, 33787152764591269, 40603596215312605,
    45928925781851997, 41928912935795581, 38603828899127916, 44319307549331863, 46087219358434844, 42320725322855635,
    35254924892186027, 40603842637512645, 38603828899127916, 32255183258371757, 40849321193777534, 42617233001179747,
    38850738967348208, 35785734991053106, 37553646799675937, 33787152764591269, 0, 0,
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
noncomputable def positiveFloor : ℝ := 119171791 / 500000000000
noncomputable def negativeCeiling : ℝ := 127755857 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 33366526216946116859002880, coefficient := (-33366526216946116859002880) }, { argument := 1115182308821086911521095680, coefficient := (-1115182308821086911521095680) }, { argument := 12356934565712633371453030400, coefficient := (-12356934565712633371453030400) }, { argument := 1115169207124972825718292480, coefficient := (-1115169207124972825718292480) }, { argument := 33346436949571185294704640, coefficient := (-33346436949571185294704640) }, { argument := 46154269981971078499532800, coefficient := (-46154269981971078499532800) }, { argument := 1881067204561313920375062528, coefficient := (-1881067204561313920375062528) }, { argument := 1881049290507507735833083904, coefficient := (-1881049290507507735833083904) }, { argument := 46162537199274645872705536, coefficient := (-46162537199274645872705536) }, { argument := 33366526216946116859002880, coefficient := (-33366526216946116859002880) }, { argument := 113633263317550260268564480, coefficient := (-113633263317550260268564480) }, { argument := 33399332477606939680833536, coefficient := (-33399332477606939680833536) }, { argument := 113633263317550260268564480, coefficient := (-113633263317550260268564480) }, { argument := 3797872278384827304278753280, coefficient := (-3797872278384827304278753280) }, { argument := 42082858436435651517113958400, coefficient := (-42082858436435651517113958400) }, { argument := 3797827659161514740369326080, coefficient := (-3797827659161514740369326080) }, { argument := 113564847175137662274109440, coefficient := (-113564847175137662274109440) }, { argument := 1881067204561313920375062528, coefficient := (-1881067204561313920375062528) }, { argument := 75420251624856670614610509824, coefficient := (-75420251624856670614610509824) }, { argument := 75419580072120451937150697472, coefficient := (-75419580072120451937150697472) }, { argument := 1881370614058800905988341760, coefficient := (-1881370614058800905988341760) }, { argument := 1115182308821086911521095680, coefficient := (-1115182308821086911521095680) }, { argument := 3797872278384827304278753280, coefficient := (-3797872278384827304278753280) }, { argument := 1116278765829216876883869696, coefficient := (-1116278765829216876883869696) }, { argument := 33399332477606939680833536, coefficient := (-33399332477606939680833536) }, { argument := 1116278765829216876883869696, coefficient := (-1116278765829216876883869696) }, { argument := 12369084011947932932510842880, coefficient := (-12369084011947932932510842880) }, { argument := 1116265651251400481917894656, coefficient := (-1116265651251400481917894656) }, { argument := 33379223458288467399671808, coefficient := (-33379223458288467399671808) }, { argument := 1881049290507507735833083904, coefficient := (-1881049290507507735833083904) }, { argument := 75419580072120451937150697472, coefficient := (-75419580072120451937150697472) }, { argument := 75418908523582714012307030016, coefficient := (-75418908523582714012307030016) }, { argument := 1881352698373565756431400960, coefficient := (-1881352698373565756431400960) }, { argument := 12356934565712633371453030400, coefficient := (-12356934565712633371453030400) }, { argument := 42082858436435651517113958400, coefficient := (-42082858436435651517113958400) }, { argument := 12369084011947932932510842880, coefficient := (-12369084011947932932510842880) }, { argument := 46162537199274645872705536, coefficient := (-46162537199274645872705536) }, { argument := 1881370614058800905988341760, coefficient := (-1881370614058800905988341760) }, { argument := 1881352698373565756431400960, coefficient := (-1881352698373565756431400960) }, { argument := 46170804994164865456144384, coefficient := (-46170804994164865456144384) }, { argument := 1115169207124972825718292480, coefficient := (-1115169207124972825718292480) }, { argument := 3797827659161514740369326080, coefficient := (-3797827659161514740369326080) }, { argument := 1116265651251400481917894656, coefficient := (-1116265651251400481917894656) }, { argument := 33346436949571185294704640, coefficient := (-33346436949571185294704640) }, { argument := 113564847175137662274109440, coefficient := (-113564847175137662274109440) }, { argument := 33379223458288467399671808, coefficient := (-33379223458288467399671808) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 29307998089650420821692252160, coefficient := 29307998089650420821692252160 }, { argument := 99811512968949362968609423360, coefficient := 99811512968949362968609423360 }, { argument := 29336813969928891396786225152, coefficient := 29336813969928891396786225152 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 7708866604500134761160769536, coefficient := 7708866604500134761160769536 }, { argument := 309204539031194474756249223168, coefficient := 309204539031194474756249223168 }, { argument := 309201781169168478883444424704, coefficient := 309201781169168478883444424704 }, { argument := 7710113309251612347497185280, coefficient := 7710113309251612347497185280 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 360798244024206633616801792, coefficient := 360798244024206633616801792 }, { argument := 12058666706070262185367437312, coefficient := 12058666706070262185367437312 }, { argument := 133617754028192435642155663360, coefficient := 133617754028192435642155663360 }, { argument := 12058525035075776096011026432, coefficient := 12058525035075776096011026432 }, { argument := 360581015165994629936971776, coefficient := 360581015165994629936971776 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk1
