import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 0, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-24247210391541598795648758448128)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    10088728999, 243353215, 243353215, 104294235, 243353215, 2746414855,
    104294235, 1264825247, 215541419, 50248065, 243353215, 50248065,
    559279245, 46827967347, 23413992147, 279631149, 46028437, 3842247295,
    153, 37809238885, 157, 5, 153, 87,
    157, 2451, 3, 1921124985, 153, 5,
    3, 5, 77, 87, 46028437, 5,
    5, 5, 5, 3, 3, 3,
    3, 50248065, 243353215, 50248065, 5, 5,
    5, 5, 21534885, 104294235, 21534885, 17325875,
    1450680525, 725340525, 8662675, 77, 77, 77,
    77, 50248065, 243353215, 50248065
  ]
def negativeCoefficients : Array ℕ := #[
    93052100936782473445813256192, 2244537238309708180981022720, 2244537238309708180981022720, 1923889061408321297983733760, 2244537238309708180981022720, 25331205975209563756785827840,
    1923889061408321297983733760, 2916488453671933728620806144, 1988018696788598674583191552, 231728298813530585180405760, 2244537238309708180981022720, 231728298813530585180405760,
    644805068640781398567813120, 53988970571383540264753692672, 53988990109944278836989394944, 644785530080042826332110848, 106134349681482931606913024, 8859619064845975664029859840,
    739862601604153054920179712, 87182169166667810644447723520, 759205414717987121715478528, 24178516392292583494123520, 739862601604153054920179712, 420706185225890952797749248,
    759205414717987121715478528, 11852308735501824428819349504, 464227514732017603087171584, 8859625232976025310661181440, 739862601604153054920179712, 24178516392292583494123520,
    464227514732017603087171584, 24178516392292583494123520, 744698304882611571619004416, 420706185225890952797749248, 106134349681482931606913024, 24178516392292583494123520,
    24178516392292583494123520, 24178516392292583494123520, 24178516392292583494123520, 464227514732017603087171584, 464227514732017603087171584, 464227514732017603087171584,
    464227514732017603087171584, 231728298813530585180405760, 2244537238309708180981022720, 231728298813530585180405760, 24178516392292583494123520, 24178516392292583494123520,
    24178516392292583494123520, 24178516392292583494123520, 198624256125883358726062080, 1923889061408321297983733760, 198624256125883358726062080, 19975373873630154850304000,
    1672520773586850689738342400, 1672521378870640608333004800, 19974768589840236255641600, 744698304882611571619004416, 744698304882611571619004416, 744698304882611571619004416,
    744698304882611571619004416, 231728298813530585180405760, 2244537238309708180981022720, 231728298813530585180405760
  ]
def negativeScales : Array ℕ := #[
    33, 27, 27, 26, 27, 31,
    26, 30, 27, 25, 27, 25,
    29, 35, 34, 28, 25, 31,
    7, 35, 7, 2, 7, 6,
    7, 11, 1, 30, 7, 2,
    1, 2, 6, 6, 25, 2,
    2, 2, 2, 1, 1, 1,
    1, 25, 27, 25, 2, 2,
    2, 2, 24, 26, 24, 24,
    30, 29, 23, 6, 6, 6,
    6, 25, 27, 25
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33232025380766896, 27858476595679667, 27858476595679667, 26636084172323563, 27858476595679667, 31354902419764618,
    26636084172323563, 30236290924516697, 27683389887135756, 25582564704911453, 27858476595679667, 25582564704911453,
    29058993551623063, 35446651365470386, 34446651887580352, 28058949835137049, 25456022117622099, 31839303232231434,
    7257387842692652, 35138019756466739, 7294620748891628, 2321928094887363, 7257387842692652, 6442943495848765,
    7294620748891628, 11259154768866840, 1584962500724866, 30839304236645700, 7257387842692652, 2321928094887363,
    1584962500724866, 2321928094887363, 6266786540694902, 6442943495848765, 25456022117622099, 2321928094887363,
    2321928094887363, 2321928094887363, 2321928094887363, 1584962500724866, 1584962500724866, 1584962500724866,
    1584962500724866, 25582564704911453, 27858476595679667, 25582564704911453, 2321928094887363, 2321928094887363,
    2321928094887363, 2321928094887363, 24360172283571542, 26636084172323563, 24360172283571542, 24046424878120007,
    30434082691967315, 29434083214077281, 23046381161633994, 6266786540694902, 6266786540694902, 6266786540694902,
    6266786540694902, 25582564704911453, 27858476595679667, 25582564704911453
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
noncomputable def negativeCeiling : ℝ := 148463353 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 93052100936782473445813256192, coefficient := (-93052100936782473445813256192) }, { argument := 2244537238309708180981022720, coefficient := (-2244537238309708180981022720) }, { argument := 2244537238309708180981022720, coefficient := (-2244537238309708180981022720) }, { argument := 1923889061408321297983733760, coefficient := (-1923889061408321297983733760) }, { argument := 2244537238309708180981022720, coefficient := (-2244537238309708180981022720) }, { argument := 25331205975209563756785827840, coefficient := (-25331205975209563756785827840) }, { argument := 1923889061408321297983733760, coefficient := (-1923889061408321297983733760) }, { argument := 2916488453671933728620806144, coefficient := (-2916488453671933728620806144) }, { argument := 1988018696788598674583191552, coefficient := (-1988018696788598674583191552) }, { argument := 231728298813530585180405760, coefficient := (-231728298813530585180405760) }, { argument := 2244537238309708180981022720, coefficient := (-2244537238309708180981022720) }, { argument := 231728298813530585180405760, coefficient := (-231728298813530585180405760) }, { argument := 644805068640781398567813120, coefficient := (-644805068640781398567813120) }, { argument := 53988970571383540264753692672, coefficient := (-53988970571383540264753692672) }, { argument := 53988990109944278836989394944, coefficient := (-53988990109944278836989394944) }, { argument := 644785530080042826332110848, coefficient := (-644785530080042826332110848) }, { argument := 106134349681482931606913024, coefficient := (-106134349681482931606913024) }, { argument := 8859619064845975664029859840, coefficient := (-8859619064845975664029859840) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 87182169166667810644447723520, coefficient := (-87182169166667810644447723520) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 420706185225890952797749248, coefficient := (-420706185225890952797749248) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 11852308735501824428819349504, coefficient := (-11852308735501824428819349504) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 8859625232976025310661181440, coefficient := (-8859625232976025310661181440) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 744698304882611571619004416, coefficient := (-744698304882611571619004416) }, { argument := 420706185225890952797749248, coefficient := (-420706185225890952797749248) }, { argument := 106134349681482931606913024, coefficient := (-106134349681482931606913024) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 231728298813530585180405760, coefficient := (-231728298813530585180405760) }, { argument := 2244537238309708180981022720, coefficient := (-2244537238309708180981022720) }, { argument := 231728298813530585180405760, coefficient := (-231728298813530585180405760) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 198624256125883358726062080, coefficient := (-198624256125883358726062080) }, { argument := 1923889061408321297983733760, coefficient := (-1923889061408321297983733760) }, { argument := 198624256125883358726062080, coefficient := (-198624256125883358726062080) }, { argument := 19975373873630154850304000, coefficient := (-19975373873630154850304000) }, { argument := 1672520773586850689738342400, coefficient := (-1672520773586850689738342400) }, { argument := 1672521378870640608333004800, coefficient := (-1672521378870640608333004800) }, { argument := 19974768589840236255641600, coefficient := (-19974768589840236255641600) }, { argument := 744698304882611571619004416, coefficient := (-744698304882611571619004416) }, { argument := 744698304882611571619004416, coefficient := (-744698304882611571619004416) }, { argument := 744698304882611571619004416, coefficient := (-744698304882611571619004416) }, { argument := 744698304882611571619004416, coefficient := (-744698304882611571619004416) }, { argument := 231728298813530585180405760, coefficient := (-231728298813530585180405760) }, { argument := 2244537238309708180981022720, coefficient := (-2244537238309708180981022720) }, { argument := 231728298813530585180405760, coefficient := (-231728298813530585180405760) }] }

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


end Parent2

namespace Parent2

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-22853710914041981847005653106688)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    87, 87, 87, 87, 567085305, 2746414855,
    567085305, 559279245, 46827967347, 23413992147, 279631149, 21534885,
    104294235, 21534885, 373545865, 31276672119, 15638341719, 186767273,
    43152747, 3540736385, 153, 34559252635, 157, 5,
    153, 87, 157, 2451, 3, 1770369415,
    153, 5, 3, 5, 77, 87,
    43152747, 46028437, 43152747, 46028437, 43152747, 109158805,
    173600007, 1264825247, 279631149, 8662675, 279631149, 186767273,
    3422041, 173600007, 1039521, 109505585, 857721321, 50248065,
    44505429, 2083141209, 567085305, 428860797, 2083141209, 50248065,
    50248065, 21534885, 50248065, 567085305
  ]
def negativeCoefficients : Array ℕ := #[
    420706185225890952797749248, 420706185225890952797749248, 420706185225890952797749248, 420706185225890952797749248, 2615219372324130889893150720, 25331205975209563756785827840,
    2615219372324130889893150720, 644805068640781398567813120, 53988970571383540264753692672, 53988990109944278836989394944, 644785530080042826332110848, 198624256125883358726062080,
    1923889061408321297983733760, 198624256125883358726062080, 430669060715466138572554240, 36059547878532500870758662144, 36059560928451011515659583488, 430656010796955493671632896,
    99503459998317204046086144, 8164382240820816416100843520, 739862601604153054920179712, 79688211092064681988739563520, 759205414717987121715478528, 24178516392292583494123520,
    739862601604153054920179712, 420706185225890952797749248, 759205414717987121715478528, 11852308735501824428819349504, 464227514732017603087171584, 8164387878606973943582556160,
    739862601604153054920179712, 24178516392292583494123520, 464227514732017603087171584, 24178516392292583494123520, 744698304882611571619004416, 420706185225890952797749248,
    99503459998317204046086144, 106134349681482931606913024, 99503459998317204046086144, 106134349681482931606913024, 99503459998317204046086144, 251703067403370821436047360,
    400294362540398334563057664, 2916488453671933728620806144, 644785530080042826332110848, 19974768589840236255641600, 644785530080042826332110848, 430656010796955493671632896,
    252502058146964430886273024, 400294362540398334563057664, 19175777846246626805415936, 252502687642105946224721920, 1977770711881384747799150592, 231728298813530585180405760,
    205245064663412804016930816, 9606793187955225117050535936, 2615219372324130889893150720, 1977771341376526263137599488, 9606793187955225117050535936, 231728298813530585180405760,
    231728298813530585180405760, 198624256125883358726062080, 231728298813530585180405760, 2615219372324130889893150720
  ]
def negativeScales : Array ℕ := #[
    6, 6, 6, 6, 29, 31,
    29, 29, 35, 34, 28, 24,
    26, 24, 28, 34, 33, 27,
    25, 31, 7, 35, 7, 2,
    7, 6, 7, 11, 1, 30,
    7, 2, 1, 2, 6, 6,
    25, 25, 25, 25, 25, 26,
    27, 30, 28, 23, 28, 27,
    21, 27, 19, 26, 29, 25,
    25, 30, 29, 28, 30, 25,
    25, 24, 25, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    6442943495848765, 6442943495848765, 6442943495848765, 6442943495848765, 29078990531027488, 31354902419764618,
    29078990531027488, 29058993551623063, 35446651365470386, 34446651887580352, 28058949835137049, 24360172283571542,
    26636084172323563, 24360172283571542, 28476710151097910, 34864367967218070, 33864368489328058, 27476666434611896,
    25362949065032558, 31721402290262447, 7257387842692652, 35008352967548682, 7294620748891628, 2321928094887363,
    7257387842692652, 6442943495848765, 7294620748891628, 11259154768866840, 1584962500724866, 30721403286492548,
    7257387842692652, 2321928094887363, 1584962500724866, 2321928094887363, 6266786540694902, 6442943495848765,
    25362949065032558, 25456022117622099, 25362949065032558, 25456022117622099, 25362949065032558, 26701853265293386,
    27371191765054480, 30236290924516697, 28058949835137049, 23046381161633994, 28058949835137049, 27476666434611896,
    21706425614490557, 27371191765054480, 19987487491947284, 26706429211167730, 29675933742390829, 25582564704911453,
    25407477998349906, 30956113503583164, 29078990531027488, 28675934201579233, 30956113503583164, 25582564704911453,
    25582564704911453, 24360172283571542, 25582564704911453, 29078990531027488
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
noncomputable def negativeCeiling : ℝ := 143147239 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 420706185225890952797749248, coefficient := (-420706185225890952797749248) }, { argument := 420706185225890952797749248, coefficient := (-420706185225890952797749248) }, { argument := 420706185225890952797749248, coefficient := (-420706185225890952797749248) }, { argument := 420706185225890952797749248, coefficient := (-420706185225890952797749248) }, { argument := 2615219372324130889893150720, coefficient := (-2615219372324130889893150720) }, { argument := 25331205975209563756785827840, coefficient := (-25331205975209563756785827840) }, { argument := 2615219372324130889893150720, coefficient := (-2615219372324130889893150720) }, { argument := 644805068640781398567813120, coefficient := (-644805068640781398567813120) }, { argument := 53988970571383540264753692672, coefficient := (-53988970571383540264753692672) }, { argument := 53988990109944278836989394944, coefficient := (-53988990109944278836989394944) }, { argument := 644785530080042826332110848, coefficient := (-644785530080042826332110848) }, { argument := 198624256125883358726062080, coefficient := (-198624256125883358726062080) }, { argument := 1923889061408321297983733760, coefficient := (-1923889061408321297983733760) }, { argument := 198624256125883358726062080, coefficient := (-198624256125883358726062080) }, { argument := 430669060715466138572554240, coefficient := (-430669060715466138572554240) }, { argument := 36059547878532500870758662144, coefficient := (-36059547878532500870758662144) }, { argument := 36059560928451011515659583488, coefficient := (-36059560928451011515659583488) }, { argument := 430656010796955493671632896, coefficient := (-430656010796955493671632896) }, { argument := 99503459998317204046086144, coefficient := (-99503459998317204046086144) }, { argument := 8164382240820816416100843520, coefficient := (-8164382240820816416100843520) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 79688211092064681988739563520, coefficient := (-79688211092064681988739563520) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 420706185225890952797749248, coefficient := (-420706185225890952797749248) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 11852308735501824428819349504, coefficient := (-11852308735501824428819349504) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 8164387878606973943582556160, coefficient := (-8164387878606973943582556160) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 744698304882611571619004416, coefficient := (-744698304882611571619004416) }, { argument := 420706185225890952797749248, coefficient := (-420706185225890952797749248) }, { argument := 99503459998317204046086144, coefficient := (-99503459998317204046086144) }, { argument := 106134349681482931606913024, coefficient := (-106134349681482931606913024) }, { argument := 99503459998317204046086144, coefficient := (-99503459998317204046086144) }, { argument := 106134349681482931606913024, coefficient := (-106134349681482931606913024) }, { argument := 99503459998317204046086144, coefficient := (-99503459998317204046086144) }, { argument := 251703067403370821436047360, coefficient := (-251703067403370821436047360) }, { argument := 400294362540398334563057664, coefficient := (-400294362540398334563057664) }, { argument := 2916488453671933728620806144, coefficient := (-2916488453671933728620806144) }, { argument := 644785530080042826332110848, coefficient := (-644785530080042826332110848) }, { argument := 19974768589840236255641600, coefficient := (-19974768589840236255641600) }, { argument := 644785530080042826332110848, coefficient := (-644785530080042826332110848) }, { argument := 430656010796955493671632896, coefficient := (-430656010796955493671632896) }, { argument := 252502058146964430886273024, coefficient := (-252502058146964430886273024) }, { argument := 400294362540398334563057664, coefficient := (-400294362540398334563057664) }, { argument := 19175777846246626805415936, coefficient := (-19175777846246626805415936) }, { argument := 252502687642105946224721920, coefficient := (-252502687642105946224721920) }, { argument := 1977770711881384747799150592, coefficient := (-1977770711881384747799150592) }, { argument := 231728298813530585180405760, coefficient := (-231728298813530585180405760) }, { argument := 205245064663412804016930816, coefficient := (-205245064663412804016930816) }, { argument := 9606793187955225117050535936, coefficient := (-9606793187955225117050535936) }, { argument := 2615219372324130889893150720, coefficient := (-2615219372324130889893150720) }, { argument := 1977771341376526263137599488, coefficient := (-1977771341376526263137599488) }, { argument := 9606793187955225117050535936, coefficient := (-9606793187955225117050535936) }, { argument := 231728298813530585180405760, coefficient := (-231728298813530585180405760) }, { argument := 231728298813530585180405760, coefficient := (-231728298813530585180405760) }, { argument := 198624256125883358726062080, coefficient := (-198624256125883358726062080) }, { argument := 231728298813530585180405760, coefficient := (-231728298813530585180405760) }, { argument := 2615219372324130889893150720, coefficient := (-2615219372324130889893150720) }] }

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

end TermShard3


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0
