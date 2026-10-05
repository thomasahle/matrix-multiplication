import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 7, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-8986268296408712134129338023936)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    23090629563, 169022549445, 8260287, 615836712885, 11832303, 2009259,
    32371395, 8260287, 11832303, 534686145, 11832303, 338046297549,
    32371395, 2009259, 11832303, 2009259, 8260287, 8260287,
    11086983693, 23090629563, 930502539301, 930709153439, 23183250817, 930502539301,
    7352113964635, 75533465, 29491474971243, 108196585, 18373005, 296009525,
    75533465, 108196585, 4889260775, 108196585, 14704285422419, 296009525,
    18373005, 108196585, 18373005, 75533465, 75533465, 448474365715,
    169022549445, 7352113964635, 7354922398945, 170838914815, 8260287, 75533465,
    302134119, 4114363, 930709153439, 7354922398945, 302134119, 29508186642449,
    432786711, 73492083, 1184039115, 302134119, 432786711, 19557059865,
    432786711, 14709902323785, 1184039115, 73492083
  ]
def negativeCoefficients : Array ℕ := #[
    6499434418479809930723328, 95151236337214154436771840, 38093850066097512747368448, 693370497667489283168010240, 27283433155448218589331456, 4633035818849697496301568,
    37321677429622563164651520, 38093850066097512747368448, 27283433155448218589331456, 616451154785834750202347520, 27283433155448218589331456, 95151573729728263454982144,
    37321677429622563164651520, 4633035818849697496301568, 27283433155448218589331456, 4633035818849697496301568, 38093850066097512747368448, 38093850066097512747368448,
    6241416953557195702665216, 6499434418479809930723328, 261913180578955244345491456, 261971337288636886610345984, 6525504983792371684605952, 261913180578955244345491456,
    4138872213939450750823301120, 1393346497855497837152829440, 33204448922774071009326661632, 997937356572180883366215680, 169461060549992980194263040, 1365102987763832340453785600,
    1393346497855497837152829440, 997937356572180883366215680, 22547735556512954864736665600, 997937356572180883366215680, 4138888396822226548098596864, 1365102987763832340453785600,
    169461060549992980194263040, 997937356572180883366215680, 169461060549992980194263040, 1393346497855497837152829440, 1393346497855497837152829440, 252468623289911693363118080,
    95151236337214154436771840, 4138872213939450750823301120, 4140453221903452065329315840, 96173759137651738573537280, 38093850066097512747368448, 1393346497855497837152829440,
    1393347692282176609846296576, 37948300643669925957730304, 261971337288636886610345984, 4140453221903452065329315840, 1393347692282176609846296576, 33223264591828090971200946176,
    997938212039937301646671872, 169461205818102560656982016, 1365104157979159516403466240, 1393347692282176609846296576, 997938212039937301646671872, 22547754885241979598526218240,
    997938212039937301646671872, 4140469414003407449971752960, 1365104157979159516403466240, 169461205818102560656982016
  ]
def negativeScales : Array ℕ := #[
    34, 37, 22, 39, 23, 20,
    24, 22, 23, 28, 23, 38,
    24, 20, 23, 20, 22, 22,
    33, 34, 39, 39, 34, 39,
    42, 26, 44, 26, 24, 28,
    26, 26, 32, 26, 43, 28,
    24, 26, 24, 26, 26, 38,
    37, 42, 42, 37, 22, 26,
    28, 21, 39, 42, 28, 44,
    28, 26, 30, 28, 28, 34,
    28, 43, 30, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34426588457413823, 37298424774305845, 22977760494171166, 39163756919455401, 23496227566572100, 20938232121984674,
    24948216212138027, 22977760494171166, 23496227566572100, 28994117074182062, 23496227566572100, 38298429889884609,
    24948216212138027, 20938232121984674, 23496227566572100, 20938232121984674, 22977760494171166, 22977760494171166,
    33368147870455918, 34426588457413823, 39759219131377581, 39759539440127445, 34432363827932943, 39759219131377581,
    42741296268755267, 26170612634381911, 44745363212139999, 26689079723372028, 24131084270195273, 28141068358767895,
    26170612634381911, 26689079723372028, 32186969209376504, 26689079723372028, 43741301909644373, 28141068358767895,
    24131084270195273, 26689079723372028, 24131084270195273, 26170612634381911, 26170612634381911, 38706234568537194,
    37298424774305845, 42741296268755267, 42741847258664795, 37313845682746969, 22977760494171166, 26170612634381911,
    28170613871111404, 21972237669294146, 39759539440127445, 42741847258664795, 28170613871111404, 44746180499740228,
    28689080960101523, 26131085506924766, 30141069595497388, 28170613871111404, 28689080960101523, 34186970446105996,
    28689080960101523, 43741852900611576, 30141069595497388, 26131085506924766
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 76232951 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 6499434418479809930723328, coefficient := (-6499434418479809930723328) }, { argument := 95151236337214154436771840, coefficient := (-95151236337214154436771840) }, { argument := 38093850066097512747368448, coefficient := (-38093850066097512747368448) }, { argument := 693370497667489283168010240, coefficient := (-693370497667489283168010240) }, { argument := 27283433155448218589331456, coefficient := (-27283433155448218589331456) }, { argument := 4633035818849697496301568, coefficient := (-4633035818849697496301568) }, { argument := 37321677429622563164651520, coefficient := (-37321677429622563164651520) }, { argument := 38093850066097512747368448, coefficient := (-38093850066097512747368448) }, { argument := 27283433155448218589331456, coefficient := (-27283433155448218589331456) }, { argument := 616451154785834750202347520, coefficient := (-616451154785834750202347520) }, { argument := 27283433155448218589331456, coefficient := (-27283433155448218589331456) }, { argument := 95151573729728263454982144, coefficient := (-95151573729728263454982144) }, { argument := 37321677429622563164651520, coefficient := (-37321677429622563164651520) }, { argument := 4633035818849697496301568, coefficient := (-4633035818849697496301568) }, { argument := 27283433155448218589331456, coefficient := (-27283433155448218589331456) }, { argument := 4633035818849697496301568, coefficient := (-4633035818849697496301568) }, { argument := 38093850066097512747368448, coefficient := (-38093850066097512747368448) }, { argument := 38093850066097512747368448, coefficient := (-38093850066097512747368448) }, { argument := 6241416953557195702665216, coefficient := (-6241416953557195702665216) }, { argument := 6499434418479809930723328, coefficient := (-6499434418479809930723328) }, { argument := 261913180578955244345491456, coefficient := (-261913180578955244345491456) }, { argument := 261971337288636886610345984, coefficient := (-261971337288636886610345984) }, { argument := 6525504983792371684605952, coefficient := (-6525504983792371684605952) }, { argument := 261913180578955244345491456, coefficient := (-261913180578955244345491456) }, { argument := 4138872213939450750823301120, coefficient := (-4138872213939450750823301120) }, { argument := 1393346497855497837152829440, coefficient := (-1393346497855497837152829440) }, { argument := 33204448922774071009326661632, coefficient := (-33204448922774071009326661632) }, { argument := 997937356572180883366215680, coefficient := (-997937356572180883366215680) }, { argument := 169461060549992980194263040, coefficient := (-169461060549992980194263040) }, { argument := 1365102987763832340453785600, coefficient := (-1365102987763832340453785600) }, { argument := 1393346497855497837152829440, coefficient := (-1393346497855497837152829440) }, { argument := 997937356572180883366215680, coefficient := (-997937356572180883366215680) }, { argument := 22547735556512954864736665600, coefficient := (-22547735556512954864736665600) }, { argument := 997937356572180883366215680, coefficient := (-997937356572180883366215680) }, { argument := 4138888396822226548098596864, coefficient := (-4138888396822226548098596864) }, { argument := 1365102987763832340453785600, coefficient := (-1365102987763832340453785600) }, { argument := 169461060549992980194263040, coefficient := (-169461060549992980194263040) }, { argument := 997937356572180883366215680, coefficient := (-997937356572180883366215680) }, { argument := 169461060549992980194263040, coefficient := (-169461060549992980194263040) }, { argument := 1393346497855497837152829440, coefficient := (-1393346497855497837152829440) }, { argument := 1393346497855497837152829440, coefficient := (-1393346497855497837152829440) }, { argument := 252468623289911693363118080, coefficient := (-252468623289911693363118080) }, { argument := 95151236337214154436771840, coefficient := (-95151236337214154436771840) }, { argument := 4138872213939450750823301120, coefficient := (-4138872213939450750823301120) }, { argument := 4140453221903452065329315840, coefficient := (-4140453221903452065329315840) }, { argument := 96173759137651738573537280, coefficient := (-96173759137651738573537280) }, { argument := 38093850066097512747368448, coefficient := (-38093850066097512747368448) }, { argument := 1393346497855497837152829440, coefficient := (-1393346497855497837152829440) }, { argument := 1393347692282176609846296576, coefficient := (-1393347692282176609846296576) }, { argument := 37948300643669925957730304, coefficient := (-37948300643669925957730304) }, { argument := 261971337288636886610345984, coefficient := (-261971337288636886610345984) }, { argument := 4140453221903452065329315840, coefficient := (-4140453221903452065329315840) }, { argument := 1393347692282176609846296576, coefficient := (-1393347692282176609846296576) }, { argument := 33223264591828090971200946176, coefficient := (-33223264591828090971200946176) }, { argument := 997938212039937301646671872, coefficient := (-997938212039937301646671872) }, { argument := 169461205818102560656982016, coefficient := (-169461205818102560656982016) }, { argument := 1365104157979159516403466240, coefficient := (-1365104157979159516403466240) }, { argument := 1393347692282176609846296576, coefficient := (-1393347692282176609846296576) }, { argument := 997938212039937301646671872, coefficient := (-997938212039937301646671872) }, { argument := 22547754885241979598526218240, coefficient := (-22547754885241979598526218240) }, { argument := 997938212039937301646671872, coefficient := (-997938212039937301646671872) }, { argument := 4140469414003407449971752960, coefficient := (-4140469414003407449971752960) }, { argument := 1365104157979159516403466240, coefficient := (-1365104157979159516403466240) }, { argument := 169461205818102560656982016, coefficient := (-169461205818102560656982016) }] }

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

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-7909385837031895843879985872896)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    432786711, 73492083, 302134119, 302134119, 448577628041, 615836712885,
    29491474971243, 29508186642449, 628145663439, 11832303, 108196585, 432786711,
    5893547, 2009259, 18373005, 73492083, 1000791, 32371395,
    296009525, 1184039115, 16123855, 8260287, 75533465, 302134119,
    4114363, 11832303, 108196585, 432786711, 5893547, 534686145,
    4889260775, 19557059865, 266321605, 11832303, 108196585, 432786711,
    5893547, 23183250817, 170838914815, 4114363, 628145663439, 5893547,
    1000791, 16123855, 4114363, 5893547, 266321605, 5893547,
    341679052439, 16123855, 1000791, 5893547, 1000791, 4114363,
    4114363, 11135018839, 338046297549, 14704285422419, 14709902323785, 341679052439,
    32371395, 296009525, 1184039115, 16123855
  ]
def negativeCoefficients : Array ℕ := #[
    997938212039937301646671872, 169461205818102560656982016, 1393347692282176609846296576, 1393347692282176609846296576, 252526754811523569698209792, 693370497667489283168010240,
    33204448922774071009326661632, 33223264591828090971200946176, 707229143949568348243623936, 27283433155448218589331456, 997937356572180883366215680, 997938212039937301646671872,
    27179188298844676699455488, 4633035818849697496301568, 169461060549992980194263040, 169461205818102560656982016, 4615333862067963967832064, 37321677429622563164651520,
    1365102987763832340453785600, 1365104157979159516403466240, 37179078333325265296424960, 38093850066097512747368448, 1393346497855497837152829440, 1393347692282176609846296576,
    37948300643669925957730304, 27283433155448218589331456, 997937356572180883366215680, 997938212039937301646671872, 27179188298844676699455488, 616451154785834750202347520,
    22547735556512954864736665600, 22547754885241979598526218240, 614095811091820761275432960, 27283433155448218589331456, 997937356572180883366215680, 997938212039937301646671872,
    27179188298844676699455488, 6525504983792371684605952, 96173759137651738573537280, 37948300643669925957730304, 707229143949568348243623936, 27179188298844676699455488,
    4615333862067963967832064, 37179078333325265296424960, 37948300643669925957730304, 27179188298844676699455488, 614095811091820761275432960, 27179188298844676699455488,
    96174103327786535154089984, 37179078333325265296424960, 4615333862067963967832064, 27179188298844676699455488, 4615333862067963967832064, 37948300643669925957730304,
    37948300643669925957730304, 6268458336760481624096768, 95151573729728263454982144, 4138888396822226548098596864, 4140469414003407449971752960, 96174103327786535154089984,
    37321677429622563164651520, 1365102987763832340453785600, 1365104157979159516403466240, 37179078333325265296424960
  ]
def negativeScales : Array ℕ := #[
    28, 26, 28, 28, 38, 39,
    44, 44, 39, 23, 26, 28,
    22, 20, 24, 26, 19, 24,
    28, 30, 23, 22, 26, 28,
    21, 23, 26, 28, 22, 28,
    32, 34, 27, 23, 26, 28,
    22, 34, 37, 21, 39, 22,
    19, 23, 21, 22, 27, 22,
    38, 23, 19, 22, 19, 21,
    21, 33, 38, 43, 43, 38,
    24, 28, 30, 23
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    28689080960101523, 26131085506924766, 28170613871111404, 28170613871111404, 38706566714382960, 39163756919455401,
    44745363212139999, 44746180499740228, 39192308194523018, 23496227566572100, 26689079723372028, 28689080960101523,
    22490704743127027, 20938232121984674, 24131084270195273, 26131085506924766, 19932709297767267, 24948216212138027,
    28141068358767895, 30141069595497388, 23942693387787790, 22977760494171166, 26170612634381911, 28170613871111404,
    21972237669294146, 23496227566572100, 26689079723372028, 28689080960101523, 22490704743127027, 28994117074182062,
    32186969209376504, 34186970446105996, 27988594248903548, 23496227566572100, 26689079723372028, 28689080960101523,
    22490704743127027, 34432363827932943, 37313845682746969, 21972237669294146, 39192308194523018, 22490704743127027,
    19932709297767267, 23942693387787790, 21972237669294146, 22490704743127027, 27988594248903548, 22490704743127027,
    38313850845907029, 23942693387787790, 19932709297767267, 22490704743127027, 19932709297767267, 21972237669294146,
    21972237669294146, 33374384947853292, 38298429889884609, 43741301909644373, 43741852900611576, 38313850845907029,
    24948216212138027, 28141068358767895, 30141069595497388, 23942693387787790
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 16636989 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 997938212039937301646671872, coefficient := (-997938212039937301646671872) }, { argument := 169461205818102560656982016, coefficient := (-169461205818102560656982016) }, { argument := 1393347692282176609846296576, coefficient := (-1393347692282176609846296576) }, { argument := 1393347692282176609846296576, coefficient := (-1393347692282176609846296576) }, { argument := 252526754811523569698209792, coefficient := (-252526754811523569698209792) }, { argument := 693370497667489283168010240, coefficient := (-693370497667489283168010240) }, { argument := 33204448922774071009326661632, coefficient := (-33204448922774071009326661632) }, { argument := 33223264591828090971200946176, coefficient := (-33223264591828090971200946176) }, { argument := 707229143949568348243623936, coefficient := (-707229143949568348243623936) }, { argument := 27283433155448218589331456, coefficient := (-27283433155448218589331456) }, { argument := 997937356572180883366215680, coefficient := (-997937356572180883366215680) }, { argument := 997938212039937301646671872, coefficient := (-997938212039937301646671872) }, { argument := 27179188298844676699455488, coefficient := (-27179188298844676699455488) }, { argument := 4633035818849697496301568, coefficient := (-4633035818849697496301568) }, { argument := 169461060549992980194263040, coefficient := (-169461060549992980194263040) }, { argument := 169461205818102560656982016, coefficient := (-169461205818102560656982016) }, { argument := 4615333862067963967832064, coefficient := (-4615333862067963967832064) }, { argument := 37321677429622563164651520, coefficient := (-37321677429622563164651520) }, { argument := 1365102987763832340453785600, coefficient := (-1365102987763832340453785600) }, { argument := 1365104157979159516403466240, coefficient := (-1365104157979159516403466240) }, { argument := 37179078333325265296424960, coefficient := (-37179078333325265296424960) }, { argument := 38093850066097512747368448, coefficient := (-38093850066097512747368448) }, { argument := 1393346497855497837152829440, coefficient := (-1393346497855497837152829440) }, { argument := 1393347692282176609846296576, coefficient := (-1393347692282176609846296576) }, { argument := 37948300643669925957730304, coefficient := (-37948300643669925957730304) }, { argument := 27283433155448218589331456, coefficient := (-27283433155448218589331456) }, { argument := 997937356572180883366215680, coefficient := (-997937356572180883366215680) }, { argument := 997938212039937301646671872, coefficient := (-997938212039937301646671872) }, { argument := 27179188298844676699455488, coefficient := (-27179188298844676699455488) }, { argument := 616451154785834750202347520, coefficient := (-616451154785834750202347520) }, { argument := 22547735556512954864736665600, coefficient := (-22547735556512954864736665600) }, { argument := 22547754885241979598526218240, coefficient := (-22547754885241979598526218240) }, { argument := 614095811091820761275432960, coefficient := (-614095811091820761275432960) }, { argument := 27283433155448218589331456, coefficient := (-27283433155448218589331456) }, { argument := 997937356572180883366215680, coefficient := (-997937356572180883366215680) }, { argument := 997938212039937301646671872, coefficient := (-997938212039937301646671872) }, { argument := 27179188298844676699455488, coefficient := (-27179188298844676699455488) }, { argument := 6525504983792371684605952, coefficient := (-6525504983792371684605952) }, { argument := 96173759137651738573537280, coefficient := (-96173759137651738573537280) }, { argument := 37948300643669925957730304, coefficient := (-37948300643669925957730304) }, { argument := 707229143949568348243623936, coefficient := (-707229143949568348243623936) }, { argument := 27179188298844676699455488, coefficient := (-27179188298844676699455488) }, { argument := 4615333862067963967832064, coefficient := (-4615333862067963967832064) }, { argument := 37179078333325265296424960, coefficient := (-37179078333325265296424960) }, { argument := 37948300643669925957730304, coefficient := (-37948300643669925957730304) }, { argument := 27179188298844676699455488, coefficient := (-27179188298844676699455488) }, { argument := 614095811091820761275432960, coefficient := (-614095811091820761275432960) }, { argument := 27179188298844676699455488, coefficient := (-27179188298844676699455488) }, { argument := 96174103327786535154089984, coefficient := (-96174103327786535154089984) }, { argument := 37179078333325265296424960, coefficient := (-37179078333325265296424960) }, { argument := 4615333862067963967832064, coefficient := (-4615333862067963967832064) }, { argument := 27179188298844676699455488, coefficient := (-27179188298844676699455488) }, { argument := 4615333862067963967832064, coefficient := (-4615333862067963967832064) }, { argument := 37948300643669925957730304, coefficient := (-37948300643669925957730304) }, { argument := 37948300643669925957730304, coefficient := (-37948300643669925957730304) }, { argument := 6268458336760481624096768, coefficient := (-6268458336760481624096768) }, { argument := 95151573729728263454982144, coefficient := (-95151573729728263454982144) }, { argument := 4138888396822226548098596864, coefficient := (-4138888396822226548098596864) }, { argument := 4140469414003407449971752960, coefficient := (-4140469414003407449971752960) }, { argument := 96174103327786535154089984, coefficient := (-96174103327786535154089984) }, { argument := 37321677429622563164651520, coefficient := (-37321677429622563164651520) }, { argument := 1365102987763832340453785600, coefficient := (-1365102987763832340453785600) }, { argument := 1365104157979159516403466240, coefficient := (-1365104157979159516403466240) }, { argument := 37179078333325265296424960, coefficient := (-37179078333325265296424960) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk7
