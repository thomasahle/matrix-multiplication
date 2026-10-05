import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 0, branch 2,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 17543746263106945150226001821696
def positiveArguments : Array ℕ := #[
    1, 17, 145, 37, 9, 53,
    9, 145, 37, 53, 2395, 53,
    145, 145, 9, 53, 9, 37,
    37, 1, 49311, 16379087, 4095943, 397085,
    44063, 599905, 3572369, 1199817, 22025
  ]
def positiveCoefficients : Array ℕ := #[
    316912650057057350374175801344, 657655645870358271040159744, 5609415803011879370636656640, 5725472681694883771408449536, 696341272098026404630757376, 4100676380132822160603348992,
    696341272098026404630757376, 5609415803011879370636656640, 5725472681694883771408449536, 4100676380132822160603348992, 92652074815265179949481328640, 4100676380132822160603348992,
    5609415803011879370636656640, 5609415803011879370636656640, 696341272098026404630757376, 4100676380132822160603348992, 696341272098026404630757376, 5725472681694883771408449536,
    5725472681694883771408449536, 618970019642690137449562112, 3725833818188561202121015296, 154696102937611857228520751104, 154740351511556345804173082624, 3750361789700586139360952320,
    416163268669370354102173696, 11331885059623658047689195520, 134960285040340412819247726592, 11331951172754418222722187264, 416040487140815743326617600
  ]
def positiveScales : Array ℕ := #[
    0, 4, 7, 5, 3, 5,
    3, 7, 5, 5, 11, 5,
    7, 7, 3, 5, 3, 5,
    5, 0, 15, 23, 21, 18,
    15, 19, 21, 20, 14
  ]
def negativeArguments : Array ℕ := #[
    2009259, 18373005, 73492083, 1000791, 11832303, 108196585,
    432786711, 5893547, 2009259, 18373005, 73492083, 1000791,
    8260287, 75533465, 302134119, 4114363, 8260287, 75533465,
    302134119, 4114363, 11086983693, 448474365715, 448577628041, 11135018839,
    1, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    4633035818849697496301568, 169461060549992980194263040, 169461205818102560656982016, 4615333862067963967832064, 27283433155448218589331456, 997937356572180883366215680,
    997938212039937301646671872, 27179188298844676699455488, 4633035818849697496301568, 169461060549992980194263040, 169461205818102560656982016, 4615333862067963967832064,
    38093850066097512747368448, 1393346497855497837152829440, 1393347692282176609846296576, 37948300643669925957730304, 38093850066097512747368448, 1393346497855497837152829440,
    1393347692282176609846296576, 37948300643669925957730304, 6241416953557195702665216, 252468623289911693363118080, 252526754811523569698209792, 6268458336760481624096768,
    158456325028528675187087900672, 316912650057057350374175801344, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    20, 24, 26, 19, 23, 26,
    28, 22, 20, 24, 26, 19,
    22, 26, 28, 21, 22, 26,
    28, 21, 33, 38, 38, 33,
    0, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 4087462841250339, 7179909090014934, 5209453365628949, 3169925001442312, 5727920454554652,
    3169925001442312, 7179909090014934, 5209453365628949, 5727920454554652, 11225809940623542, 5727920454554652,
    7179909090014934, 7179909090014934, 3169925001442312, 5727920454554652, 3169925001442312, 5209453365628949,
    5209453365628949, 0, 15589621889748028, 23965351604163281, 21965764207118307, 18599088338108356,
    15427280102862913, 19194374530357469, 21768449677471103, 20194382947386688, 14426854398695136
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    20938232121984674, 24131084270195273, 26131085506924766, 19932709297767267, 23496227566572100, 26689079723372028,
    28689080960101523, 22490704743127027, 20938232121984674, 24131084270195273, 26131085506924766, 19932709297767267,
    22977760494171166, 26170612634381911, 28170613871111404, 21972237669294146, 22977760494171166, 26170612634381911,
    28170613871111404, 21972237669294146, 33368147870455918, 38706234568537194, 38706566714382960, 33374384947853292,
    0, 0, 0
  ]

abbrev PositiveTerm := Fin 29
abbrev NegativeTerm := Fin 27
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
noncomputable def positiveFloor : ℝ := 145128393 / 1000000000000
noncomputable def negativeCeiling : ℝ := 2994147 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4633035818849697496301568, coefficient := (-4633035818849697496301568) }, { argument := 169461060549992980194263040, coefficient := (-169461060549992980194263040) }, { argument := 169461205818102560656982016, coefficient := (-169461205818102560656982016) }, { argument := 4615333862067963967832064, coefficient := (-4615333862067963967832064) }, { argument := 27283433155448218589331456, coefficient := (-27283433155448218589331456) }, { argument := 997937356572180883366215680, coefficient := (-997937356572180883366215680) }, { argument := 997938212039937301646671872, coefficient := (-997938212039937301646671872) }, { argument := 27179188298844676699455488, coefficient := (-27179188298844676699455488) }, { argument := 4633035818849697496301568, coefficient := (-4633035818849697496301568) }, { argument := 169461060549992980194263040, coefficient := (-169461060549992980194263040) }, { argument := 169461205818102560656982016, coefficient := (-169461205818102560656982016) }, { argument := 4615333862067963967832064, coefficient := (-4615333862067963967832064) }, { argument := 38093850066097512747368448, coefficient := (-38093850066097512747368448) }, { argument := 1393346497855497837152829440, coefficient := (-1393346497855497837152829440) }, { argument := 1393347692282176609846296576, coefficient := (-1393347692282176609846296576) }, { argument := 37948300643669925957730304, coefficient := (-37948300643669925957730304) }, { argument := 38093850066097512747368448, coefficient := (-38093850066097512747368448) }, { argument := 1393346497855497837152829440, coefficient := (-1393346497855497837152829440) }, { argument := 1393347692282176609846296576, coefficient := (-1393347692282176609846296576) }, { argument := 37948300643669925957730304, coefficient := (-37948300643669925957730304) }, { argument := 6241416953557195702665216, coefficient := (-6241416953557195702665216) }, { argument := 252468623289911693363118080, coefficient := (-252468623289911693363118080) }, { argument := 252526754811523569698209792, coefficient := (-252526754811523569698209792) }, { argument := 6268458336760481624096768, coefficient := (-6268458336760481624096768) }, { argument := 316912650057057350374175801344, coefficient := 316912650057057350374175801344 }, { argument := 657655645870358271040159744, coefficient := 657655645870358271040159744 }, { argument := 5609415803011879370636656640, coefficient := 5609415803011879370636656640 }, { argument := 5725472681694883771408449536, coefficient := 5725472681694883771408449536 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 4100676380132822160603348992, coefficient := 4100676380132822160603348992 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 5609415803011879370636656640, coefficient := 5609415803011879370636656640 }, { argument := 5725472681694883771408449536, coefficient := 5725472681694883771408449536 }, { argument := 4100676380132822160603348992, coefficient := 4100676380132822160603348992 }, { argument := 92652074815265179949481328640, coefficient := 92652074815265179949481328640 }, { argument := 4100676380132822160603348992, coefficient := 4100676380132822160603348992 }, { argument := 5609415803011879370636656640, coefficient := 5609415803011879370636656640 }, { argument := 5609415803011879370636656640, coefficient := 5609415803011879370636656640 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 4100676380132822160603348992, coefficient := 4100676380132822160603348992 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 5725472681694883771408449536, coefficient := 5725472681694883771408449536 }, { argument := 5725472681694883771408449536, coefficient := 5725472681694883771408449536 }, { argument := 618970019642690137449562112, coefficient := 618970019642690137449562112 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 3725833818188561202121015296, coefficient := 3725833818188561202121015296 }, { argument := 154696102937611857228520751104, coefficient := 154696102937611857228520751104 }, { argument := 154740351511556345804173082624, coefficient := 154740351511556345804173082624 }, { argument := 3750361789700586139360952320, coefficient := 3750361789700586139360952320 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 416163268669370354102173696, coefficient := 416163268669370354102173696 }, { argument := 11331885059623658047689195520, coefficient := 11331885059623658047689195520 }, { argument := 134960285040340412819247726592, coefficient := 134960285040340412819247726592 }, { argument := 11331951172754418222722187264, coefficient := 11331951172754418222722187264 }, { argument := 416040487140815743326617600, coefficient := 416040487140815743326617600 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end TermShard2


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk7
