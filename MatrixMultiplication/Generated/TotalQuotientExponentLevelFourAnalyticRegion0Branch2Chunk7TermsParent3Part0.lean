import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 7, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 233202417730621647883513888768
def positiveArguments : Array ℕ := #[
    11, 16777185, 16777247, 27172889, 96654451, 6791901,
    1863835, 36811779, 36820719, 1866113, 42211, 1130329,
    28869291, 2256571, 41745
  ]
def positiveCoefficients : Array ℕ := #[
    1743019575313815427057966907392, 158456032241806737269084651520, 158456617815250613105091149824, 256640680512674541722285375488, 912875479645132925389129121792, 256590765098950609572376608768,
    17603423867198690373738168320, 695354845297618661659939700736, 695523717123046080172781469696, 17624938968894644477331767296, 797343246433642376461287424, 21351311136862252819007143936,
    272662744405220605481894019072, 21312710513231276339030392832, 788540755309573357782958080
  ]
def positiveScales : Array ℕ := #[
    3, 23, 24, 24, 26, 22,
    20, 25, 25, 20, 15, 20,
    24, 21, 15
  ]
def negativeArguments : Array ℕ := #[
    708181906047, 9481872185913, 60543176551047, 18929460360369, 350181887265, 5633189939789,
    222279592040083, 222333078499269, 5639567617883, 5633189939789, 20005322583913, 2815724929829,
    708181906047, 708184223105, 708184223105, 9481901598151, 60543406167417, 18929518725967,
    350182994655, 20005322583913, 395340897635191, 49429671833529, 20030734597657, 222279592040083,
    395340897635191, 222236947944063, 9481872185913, 9481901598151, 2815724929829, 222236947944063,
    222290484040875, 1409469666467, 222333078499269, 49429671833529, 222290484040875, 60543176551047,
    60543406167417, 5639567617883, 20030734597657, 1409469666467, 18929460360369, 18929518725967,
    350181887265, 350182994655, 1, 9, 9, 1
  ]
def negativeCoefficients : Array ℕ := #[
    199335485511487300495736832, 5337819505406557146480377856, 68165556838780355099731427328, 5328169414080150208002392064, 197134877124818879832391680, 1585602007108810449914691584,
    62566142992736479223845224448, 62581198092590194026520510464, 1587397163901787160862261248, 1585602007108810449914691584, 5630997708396072187281276928, 1585112218094462549673115648,
    199335485511487300495736832, 199336137705333887734906880, 199336137705333887734906880, 5337836063024569263023194112, 68165815363829947641215582208, 5328185842535487961512804352,
    197135500529967799059087360, 5630997708396072187281276928, 222557139909270448860500590592, 222611451650527106189318160384, 5638150554372835457464532992, 62566142992736479223845224448,
    222557139909270448860500590592, 62554139746802402745624035328, 5337819505406557146480377856, 5337836063024569263023194112, 1585112218094462549673115648, 62554139746802402745624035328,
    62569208818405739870552064000, 1586921766172699620339089408, 62581198092590194026520510464, 222611451650527106189318160384, 62569208818405739870552064000, 68165556838780355099731427328,
    68165815363829947641215582208, 1587397163901787160862261248, 5638150554372835457464532992, 1586921766172699620339089408, 5328169414080150208002392064, 5328185842535487961512804352,
    197134877124818879832391680, 197135500529967799059087360, 316912650057057350374175801344, 1426106925256758076683791106048, 1426106925256758076683791106048, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    39, 43, 45, 44, 38, 42,
    47, 47, 42, 42, 44, 41,
    39, 39, 39, 43, 45, 44,
    38, 44, 48, 45, 44, 47,
    48, 47, 43, 43, 41, 47,
    47, 40, 47, 45, 47, 45,
    45, 42, 44, 40, 44, 44,
    38, 38, 0, 3, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3459431618637292, 23999997332806929, 24000002665728625, 24695664624114032, 26526332835217785, 22695383999375702,
    20829842717216840, 25133664136630057, 25134014462751790, 20831604918570322, 15365331387427179, 20108311322128413,
    24783032341090630, 21105700741066000, 15349315788940125
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    39365329027295327, 43108309084550425, 45783029605790290, 44105698516921935, 38349313507804443, 42357089255809304,
    47659368826009243, 47659715935549569, 42358721694987248, 42357089255809304, 44185449125726317, 41356643541602653,
    39365329027295327, 39365333747555177, 39365333747555177, 43108313559702933, 45783035077352771, 44105702965206639,
    38349318070072205, 44185449125726317, 48490090536713798, 45490442561908962, 44187280564369969, 47659368826009243,
    48490090536713798, 47659092019993954, 43108309084550425, 43108313559702933, 41356643541602653, 47659092019993954,
    47659439518286511, 40358289568306571, 47659715935549569, 45490442561908962, 47659439518286511, 45783029605790290,
    45783035077352771, 42358721694987248, 44187280564369969, 40358289568306571, 44105698516921935, 44105702965206639,
    38349313507804443, 38349318070072205, 0, 3169925001442313, 3169925001442313, 0
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 48
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
noncomputable def positiveFloor : ℝ := 1123842851 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1091317391 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 199335485511487300495736832, coefficient := (-199335485511487300495736832) }, { argument := 5337819505406557146480377856, coefficient := (-5337819505406557146480377856) }, { argument := 68165556838780355099731427328, coefficient := (-68165556838780355099731427328) }, { argument := 5328169414080150208002392064, coefficient := (-5328169414080150208002392064) }, { argument := 197134877124818879832391680, coefficient := (-197134877124818879832391680) }, { argument := 1585602007108810449914691584, coefficient := (-1585602007108810449914691584) }, { argument := 62566142992736479223845224448, coefficient := (-62566142992736479223845224448) }, { argument := 62581198092590194026520510464, coefficient := (-62581198092590194026520510464) }, { argument := 1587397163901787160862261248, coefficient := (-1587397163901787160862261248) }, { argument := 1585602007108810449914691584, coefficient := (-1585602007108810449914691584) }, { argument := 5630997708396072187281276928, coefficient := (-5630997708396072187281276928) }, { argument := 1585112218094462549673115648, coefficient := (-1585112218094462549673115648) }, { argument := 199335485511487300495736832, coefficient := (-199335485511487300495736832) }, { argument := 199336137705333887734906880, coefficient := (-199336137705333887734906880) }, { argument := 199336137705333887734906880, coefficient := (-199336137705333887734906880) }, { argument := 5337836063024569263023194112, coefficient := (-5337836063024569263023194112) }, { argument := 68165815363829947641215582208, coefficient := (-68165815363829947641215582208) }, { argument := 5328185842535487961512804352, coefficient := (-5328185842535487961512804352) }, { argument := 197135500529967799059087360, coefficient := (-197135500529967799059087360) }, { argument := 5630997708396072187281276928, coefficient := (-5630997708396072187281276928) }, { argument := 222557139909270448860500590592, coefficient := (-222557139909270448860500590592) }, { argument := 222611451650527106189318160384, coefficient := (-222611451650527106189318160384) }, { argument := 5638150554372835457464532992, coefficient := (-5638150554372835457464532992) }, { argument := 62566142992736479223845224448, coefficient := (-62566142992736479223845224448) }, { argument := 222557139909270448860500590592, coefficient := (-222557139909270448860500590592) }, { argument := 62554139746802402745624035328, coefficient := (-62554139746802402745624035328) }, { argument := 5337819505406557146480377856, coefficient := (-5337819505406557146480377856) }, { argument := 5337836063024569263023194112, coefficient := (-5337836063024569263023194112) }, { argument := 1585112218094462549673115648, coefficient := (-1585112218094462549673115648) }, { argument := 62554139746802402745624035328, coefficient := (-62554139746802402745624035328) }, { argument := 62569208818405739870552064000, coefficient := (-62569208818405739870552064000) }, { argument := 1586921766172699620339089408, coefficient := (-1586921766172699620339089408) }, { argument := 62581198092590194026520510464, coefficient := (-62581198092590194026520510464) }, { argument := 222611451650527106189318160384, coefficient := (-222611451650527106189318160384) }, { argument := 62569208818405739870552064000, coefficient := (-62569208818405739870552064000) }, { argument := 68165556838780355099731427328, coefficient := (-68165556838780355099731427328) }, { argument := 68165815363829947641215582208, coefficient := (-68165815363829947641215582208) }, { argument := 1587397163901787160862261248, coefficient := (-1587397163901787160862261248) }, { argument := 5638150554372835457464532992, coefficient := (-5638150554372835457464532992) }, { argument := 1586921766172699620339089408, coefficient := (-1586921766172699620339089408) }, { argument := 5328169414080150208002392064, coefficient := (-5328169414080150208002392064) }, { argument := 5328185842535487961512804352, coefficient := (-5328185842535487961512804352) }, { argument := 197134877124818879832391680, coefficient := (-197134877124818879832391680) }, { argument := 197135500529967799059087360, coefficient := (-197135500529967799059087360) }, { argument := 1743019575313815427057966907392, coefficient := 1743019575313815427057966907392 }, { argument := 158456032241806737269084651520, coefficient := 158456032241806737269084651520 }, { argument := 158456617815250613105091149824, coefficient := 158456617815250613105091149824 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 256640680512674541722285375488, coefficient := 256640680512674541722285375488 }, { argument := 912875479645132925389129121792, coefficient := 912875479645132925389129121792 }, { argument := 256590765098950609572376608768, coefficient := 256590765098950609572376608768 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 17603423867198690373738168320, coefficient := 17603423867198690373738168320 }, { argument := 695354845297618661659939700736, coefficient := 695354845297618661659939700736 }, { argument := 695523717123046080172781469696, coefficient := 695523717123046080172781469696 }, { argument := 17624938968894644477331767296, coefficient := 17624938968894644477331767296 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 797343246433642376461287424, coefficient := 797343246433642376461287424 }, { argument := 21351311136862252819007143936, coefficient := 21351311136862252819007143936 }, { argument := 272662744405220605481894019072, coefficient := 272662744405220605481894019072 }, { argument := 21312710513231276339030392832, coefficient := 21312710513231276339030392832 }, { argument := 788540755309573357782958080, coefficient := 788540755309573357782958080 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk7
