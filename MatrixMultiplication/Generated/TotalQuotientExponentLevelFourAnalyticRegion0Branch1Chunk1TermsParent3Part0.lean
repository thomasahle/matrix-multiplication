import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 1, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk1

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
def constantNumerator : ℤ := 18748327622477988589077260140544
def positiveArguments : Array ℕ := #[
    3, 7013, 8160387, 2041047, 228225, 59345
  ]
def positiveCoefficients : Array ℕ := #[
    475368975085586025561263702016, 2119549193239348600553603072, 77072676112090350992914120704, 77108575542093126035828637696, 2155524181105849557791539200, 1120995355703596380827156480
  ]
def positiveScales : Array ℕ := #[
    1, 12, 22, 20, 17, 15
  ]
def negativeArguments : Array ℕ := #[
    278338957, 57715650517, 57726324303, 137910645, 215879979, 40172429453,
    831499653303, 40172734841, 1726861797, 323877599643, 67158426376083, 67170846485097,
    160474010355, 40172429453, 927929009987, 38198447732119, 1855872232183, 80336672341,
    278338957, 323877599643, 81007114383, 9058022025, 81007114383, 16797426970023,
    16800533443557, 40137189255, 831499653303, 38198447732119, 97833282343221, 19099370991557,
    207853929813, 57715650517, 67158426376083, 16797426970023, 1878248159025, 9058022025,
    1878248159025, 1878595517475, 4488044625, 40172734841, 1855872232183, 19099370991557,
    463971611125, 40168641527, 57726324303, 67170846485097, 16800533443557, 1878595517475,
    1726861797, 80336672341, 207853929813, 40168641527, 431670945, 137910645,
    160474010355, 40137189255, 4488044625, 1
  ]
def negativeCoefficients : Array ℕ := #[
    10028217784223140073701376, 519856364323613949625892864, 519952505240918414459928576, 9937509270918796117278720, 972236992981150501699584, 45230134578774584613404672,
    468092691096760926691393536, 45230478415095335468662784, 972136768186193138417664, 364653759266466372079583232, 18903416500132268053729640448, 18906912450027727512385093632,
    361355346618713558262743040, 45230134578774584613404672, 2089510371801863230666571776, 21503814371562812051321520128, 2089526373326652358568968192, 45225525952389154070331392,
    10028217784223140073701376, 364653759266466372079583232, 364823610149637946991443968, 10198426154125936400793600, 364823610149637946991443968, 18912221460744675621026660352,
    18915719039007215297985773568, 361523661145034151910440960, 468092691096760926691393536, 21503814371562812051321520128, 220300966952681310676800503808, 21503980020146741476031725568,
    468045440426660014665498624, 519856364323613949625892864, 18903416500132268053729640448, 18912221460744675621026660352, 528679856818394382100070400, 10198426154125936400793600,
    528679856818394382100070400, 528777629530018381666713600, 10106178050386078728192000, 45230478415095335468662784, 2089526373326652358568968192, 21503980020146741476031725568,
    2089542374973038676410368000, 45225869753244057860046848, 519952505240918414459928576, 18906912450027727512385093632, 18915719039007215297985773568, 528777629530018381666713600,
    972136768186193138417664, 45225525952389154070331392, 468045440426660014665498624, 45225869753244057860046848, 972036553524334936719360, 9937509270918796117278720,
    361355346618713558262743040, 361523661145034151910440960, 10106178050386078728192000, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    28, 35, 35, 27, 27, 35,
    39, 35, 30, 38, 45, 45,
    37, 35, 39, 45, 40, 36,
    28, 38, 36, 33, 36, 43,
    43, 35, 39, 45, 46, 44,
    37, 35, 45, 43, 40, 33,
    40, 40, 32, 35, 40, 44,
    38, 35, 35, 45, 43, 40,
    30, 36, 37, 35, 28, 27,
    37, 35, 32, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 12775816012648766, 22960206141068884, 20960877972816958, 17800097308970370, 15856838862890622
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    28052267605020899, 35748243530728016, 35748510314422089, 27039158578503300, 27685654211233558, 35225486660787517,
    39596924705741565, 35225497628012664, 30685505480760176, 38236657734180288, 45932633667422219, 45932900451150742,
    37223548707662689, 35225486660787517, 39755223482062735, 45118579246281667, 40755234530216649, 36225339653018223,
    28052267605020899, 38236657734180288, 36237329565936952, 33076548901358349, 36237329565936952, 43933305499269123,
    43933572282998033, 35224220539419352, 39596924705741565, 45118579246281667, 46475390579113668, 44118590359634209,
    37596779068457481, 35748243530728016, 45932633667422219, 43933305499269123, 40772524827214126, 33076548901358349,
    40772524827214126, 40772791610908998, 32063439874840750, 35225497628012664, 40755234530216649, 44118590359634209,
    38755245578369912, 35225350620229609, 35748510314422089, 45932900451150742, 43933572282998033, 40772791610908998,
    30685505480760176, 36225339653018223, 37596779068457481, 35225350620229609, 28685356749991804, 27039158578503300,
    37223548707662689, 35224220539419352, 32063439874840750, 0
  ]

abbrev PositiveTerm := Fin 6
abbrev NegativeTerm := Fin 58
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
noncomputable def positiveFloor : ℝ := 50826891 / 1000000000000
noncomputable def negativeCeiling : ℝ := 129777781 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 10028217784223140073701376, coefficient := (-10028217784223140073701376) }, { argument := 519856364323613949625892864, coefficient := (-519856364323613949625892864) }, { argument := 519952505240918414459928576, coefficient := (-519952505240918414459928576) }, { argument := 9937509270918796117278720, coefficient := (-9937509270918796117278720) }, { argument := 972236992981150501699584, coefficient := (-972236992981150501699584) }, { argument := 45230134578774584613404672, coefficient := (-45230134578774584613404672) }, { argument := 468092691096760926691393536, coefficient := (-468092691096760926691393536) }, { argument := 45230478415095335468662784, coefficient := (-45230478415095335468662784) }, { argument := 972136768186193138417664, coefficient := (-972136768186193138417664) }, { argument := 364653759266466372079583232, coefficient := (-364653759266466372079583232) }, { argument := 18903416500132268053729640448, coefficient := (-18903416500132268053729640448) }, { argument := 18906912450027727512385093632, coefficient := (-18906912450027727512385093632) }, { argument := 361355346618713558262743040, coefficient := (-361355346618713558262743040) }, { argument := 45230134578774584613404672, coefficient := (-45230134578774584613404672) }, { argument := 2089510371801863230666571776, coefficient := (-2089510371801863230666571776) }, { argument := 21503814371562812051321520128, coefficient := (-21503814371562812051321520128) }, { argument := 2089526373326652358568968192, coefficient := (-2089526373326652358568968192) }, { argument := 45225525952389154070331392, coefficient := (-45225525952389154070331392) }, { argument := 10028217784223140073701376, coefficient := (-10028217784223140073701376) }, { argument := 364653759266466372079583232, coefficient := (-364653759266466372079583232) }, { argument := 364823610149637946991443968, coefficient := (-364823610149637946991443968) }, { argument := 10198426154125936400793600, coefficient := (-10198426154125936400793600) }, { argument := 364823610149637946991443968, coefficient := (-364823610149637946991443968) }, { argument := 18912221460744675621026660352, coefficient := (-18912221460744675621026660352) }, { argument := 18915719039007215297985773568, coefficient := (-18915719039007215297985773568) }, { argument := 361523661145034151910440960, coefficient := (-361523661145034151910440960) }, { argument := 468092691096760926691393536, coefficient := (-468092691096760926691393536) }, { argument := 21503814371562812051321520128, coefficient := (-21503814371562812051321520128) }, { argument := 220300966952681310676800503808, coefficient := (-220300966952681310676800503808) }, { argument := 21503980020146741476031725568, coefficient := (-21503980020146741476031725568) }, { argument := 468045440426660014665498624, coefficient := (-468045440426660014665498624) }, { argument := 519856364323613949625892864, coefficient := (-519856364323613949625892864) }, { argument := 18903416500132268053729640448, coefficient := (-18903416500132268053729640448) }, { argument := 18912221460744675621026660352, coefficient := (-18912221460744675621026660352) }, { argument := 528679856818394382100070400, coefficient := (-528679856818394382100070400) }, { argument := 10198426154125936400793600, coefficient := (-10198426154125936400793600) }, { argument := 528679856818394382100070400, coefficient := (-528679856818394382100070400) }, { argument := 528777629530018381666713600, coefficient := (-528777629530018381666713600) }, { argument := 10106178050386078728192000, coefficient := (-10106178050386078728192000) }, { argument := 45230478415095335468662784, coefficient := (-45230478415095335468662784) }, { argument := 2089526373326652358568968192, coefficient := (-2089526373326652358568968192) }, { argument := 21503980020146741476031725568, coefficient := (-21503980020146741476031725568) }, { argument := 2089542374973038676410368000, coefficient := (-2089542374973038676410368000) }, { argument := 45225869753244057860046848, coefficient := (-45225869753244057860046848) }, { argument := 519952505240918414459928576, coefficient := (-519952505240918414459928576) }, { argument := 18906912450027727512385093632, coefficient := (-18906912450027727512385093632) }, { argument := 18915719039007215297985773568, coefficient := (-18915719039007215297985773568) }, { argument := 528777629530018381666713600, coefficient := (-528777629530018381666713600) }, { argument := 972136768186193138417664, coefficient := (-972136768186193138417664) }, { argument := 45225525952389154070331392, coefficient := (-45225525952389154070331392) }, { argument := 468045440426660014665498624, coefficient := (-468045440426660014665498624) }, { argument := 45225869753244057860046848, coefficient := (-45225869753244057860046848) }, { argument := 972036553524334936719360, coefficient := (-972036553524334936719360) }, { argument := 9937509270918796117278720, coefficient := (-9937509270918796117278720) }, { argument := 361355346618713558262743040, coefficient := (-361355346618713558262743040) }, { argument := 361523661145034151910440960, coefficient := (-361523661145034151910440960) }, { argument := 10106178050386078728192000, coefficient := (-10106178050386078728192000) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 2119549193239348600553603072, coefficient := 2119549193239348600553603072 }, { argument := 77072676112090350992914120704, coefficient := 77072676112090350992914120704 }, { argument := 77108575542093126035828637696, coefficient := 77108575542093126035828637696 }, { argument := 2155524181105849557791539200, coefficient := 2155524181105849557791539200 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1120995355703596380827156480, coefficient := 1120995355703596380827156480 }] }

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

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-19620987587169234638670456160256)
def positiveArguments : Array ℕ := #[
    2728855, 27978017, 682219, 59339, 39689, 8229809,
    8231331, 19665
  ]
def positiveCoefficients : Array ℕ := #[
    51546613554444982758481592320, 528489798951828570291021283328, 51547010233229543808679542784, 1120882018908007509342027776, 1499408026708906791091044352, 77728348364037904012964528128,
    77742723247611759212995018752, 1485845390170105170037309440
  ]
def positiveScales : Array ℕ := #[
    21, 24, 19, 15, 15, 22,
    22, 14
  ]
def negativeArguments : Array ℕ := #[
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    633825300114114700748351602688, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    21379864307161366, 24737790376322966, 19379875409429271, 15856692993687819, 15276451592347871, 22972427516903994,
    22972694300592695, 14263342565830272
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0
  ]

abbrev PositiveTerm := Fin 8
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 22639481 / 100000000000
noncomputable def negativeCeiling : ℝ := 0 / 1

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 51546613554444982758481592320, coefficient := 51546613554444982758481592320 }, { argument := 528489798951828570291021283328, coefficient := 528489798951828570291021283328 }, { argument := 51547010233229543808679542784, coefficient := 51547010233229543808679542784 }, { argument := 1120882018908007509342027776, coefficient := 1120882018908007509342027776 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 1499408026708906791091044352, coefficient := 1499408026708906791091044352 }, { argument := 77728348364037904012964528128, coefficient := 77728348364037904012964528128 }, { argument := 77742723247611759212995018752, coefficient := 77742723247611759212995018752 }, { argument := 1485845390170105170037309440, coefficient := 1485845390170105170037309440 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk1
