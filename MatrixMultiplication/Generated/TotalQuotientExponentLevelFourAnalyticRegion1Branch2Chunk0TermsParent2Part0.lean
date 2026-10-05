import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
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

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-59068321180202882085385790291968)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    699099, 46028437, 43152747, 46028437, 43152747, 12233361,
    3842247295, 3540736385, 3842247295, 3540736385, 153, 153,
    153, 153, 218318135, 347210535, 2529668155, 559279245,
    17325875, 559279245, 373545865, 109505585, 347210535, 2079105,
    12233367, 37809238885, 34559252635, 37809238885, 34559252635, 157,
    157, 157, 157, 1657415421, 29071637721, 50803342173,
    46827967347, 1450680525, 46827967347, 31276672119, 857721321, 29071637721,
    174081663, 5, 5, 5, 5, 50248065,
    243353215, 50248065, 218318135, 1657415421, 50248065, 44505429,
    2083141209, 567085305, 828707973, 2083141209, 50248065, 50248065,
    21534885, 50248065, 567085305, 21534885
  ]
def negativeCoefficients : Array ℕ := #[
    3301401685807686099249659904, 106134349681482931606913024, 99503459998317204046086144, 106134349681482931606913024, 99503459998317204046086144, 115540827918489371682130624512,
    8859619064845975664029859840, 8164382240820816416100843520, 8859619064845975664029859840, 8164382240820816416100843520, 739862601604153054920179712, 739862601604153054920179712,
    739862601604153054920179712, 739862601604153054920179712, 251703672687160740030709760, 400306492427548303200092160, 2916508815418626590145249280, 644805068640781398567813120,
    19975373873630154850304000, 644805068640781398567813120, 430669060715466138572554240, 252502687642105946224721920, 400306492427548303200092160, 19176358918684948656291840,
    115540884586887166117873188864, 87182169166667810644447723520, 79688211092064681988739563520, 87182169166667810644447723520, 79688211092064681988739563520, 759205414717987121715478528,
    759205414717987121715478528, 759205414717987121715478528, 759205414717987121715478528, 1910869880937910720209616896, 33517316302680487822356381696, 58572265697151642760378318848,
    53988970571383540264753692672, 1672520773586850689738342400, 53988970571383540264753692672, 36059547878532500870758662144, 1977770711881384747799150592, 33517316302680487822356381696,
    1605619942643376662148808704, 24178516392292583494123520, 24178516392292583494123520, 24178516392292583494123520, 24178516392292583494123520, 231728298813530585180405760,
    2244537238309708180981022720, 231728298813530585180405760, 251703672687160740030709760, 1910869880937910720209616896, 231728298813530585180405760, 205245064663412804016930816,
    9606793187955225117050535936, 2615219372324130889893150720, 1910870486221700638804279296, 9606793187955225117050535936, 231728298813530585180405760, 231728298813530585180405760,
    198624256125883358726062080, 231728298813530585180405760, 2615219372324130889893150720, 198624256125883358726062080
  ]
def negativeScales : Array ℕ := #[
    19, 25, 25, 25, 25, 23,
    31, 31, 31, 31, 7, 7,
    7, 7, 27, 28, 31, 29,
    24, 29, 28, 26, 28, 20,
    23, 35, 35, 35, 35, 7,
    7, 7, 7, 30, 34, 35,
    35, 30, 35, 34, 29, 34,
    27, 2, 2, 2, 2, 25,
    27, 25, 27, 30, 25, 25,
    30, 29, 29, 30, 25, 25,
    24, 25, 29, 24
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19415137245768091, 25456022117622099, 25362949065032558, 25456022117622099, 25362949065032558, 23544317489327099,
    31839303232231434, 31721402290262447, 31839303232231434, 31721402290262447, 7257387842692652, 7257387842692652,
    7257387842692652, 7257387842692652, 27701856734614927, 28371235481540493, 31236300996796735, 29058993551623063,
    24046424878120007, 29058993551623063, 28476710151097910, 26706429211167730, 28371235481540493, 20987531208446993,
    23544318196914173, 35138019756466739, 35008352967548682, 35138019756466739, 35008352967548682, 7294620748891628,
    7294620748891628, 7294620748891628, 7294620748891628, 30626288104536405, 34758893295660562, 35564204358822053,
    35446651365470386, 30434082691967315, 35446651365470386, 34864367967218070, 29675933742390829, 34758893295660562,
    27375189002913723, 2321928094887363, 2321928094887363, 2321928094887363, 2321928094887363, 25582564704911453,
    27858476595679667, 25582564704911453, 27701856734614927, 30626288104536405, 25582564704911453, 25407477998349906,
    30956113503583164, 29078990531027488, 29626288561521882, 30956113503583164, 25582564704911453, 25582564704911453,
    24360172283571542, 25582564704911453, 29078990531027488, 24360172283571542
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
noncomputable def negativeCeiling : ℝ := 175846423 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3301401685807686099249659904, coefficient := (-3301401685807686099249659904) }, { argument := 106134349681482931606913024, coefficient := (-106134349681482931606913024) }, { argument := 99503459998317204046086144, coefficient := (-99503459998317204046086144) }, { argument := 106134349681482931606913024, coefficient := (-106134349681482931606913024) }, { argument := 99503459998317204046086144, coefficient := (-99503459998317204046086144) }, { argument := 115540827918489371682130624512, coefficient := (-115540827918489371682130624512) }, { argument := 8859619064845975664029859840, coefficient := (-8859619064845975664029859840) }, { argument := 8164382240820816416100843520, coefficient := (-8164382240820816416100843520) }, { argument := 8859619064845975664029859840, coefficient := (-8859619064845975664029859840) }, { argument := 8164382240820816416100843520, coefficient := (-8164382240820816416100843520) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 251703672687160740030709760, coefficient := (-251703672687160740030709760) }, { argument := 400306492427548303200092160, coefficient := (-400306492427548303200092160) }, { argument := 2916508815418626590145249280, coefficient := (-2916508815418626590145249280) }, { argument := 644805068640781398567813120, coefficient := (-644805068640781398567813120) }, { argument := 19975373873630154850304000, coefficient := (-19975373873630154850304000) }, { argument := 644805068640781398567813120, coefficient := (-644805068640781398567813120) }, { argument := 430669060715466138572554240, coefficient := (-430669060715466138572554240) }, { argument := 252502687642105946224721920, coefficient := (-252502687642105946224721920) }, { argument := 400306492427548303200092160, coefficient := (-400306492427548303200092160) }, { argument := 19176358918684948656291840, coefficient := (-19176358918684948656291840) }, { argument := 115540884586887166117873188864, coefficient := (-115540884586887166117873188864) }, { argument := 87182169166667810644447723520, coefficient := (-87182169166667810644447723520) }, { argument := 79688211092064681988739563520, coefficient := (-79688211092064681988739563520) }, { argument := 87182169166667810644447723520, coefficient := (-87182169166667810644447723520) }, { argument := 79688211092064681988739563520, coefficient := (-79688211092064681988739563520) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 1910869880937910720209616896, coefficient := (-1910869880937910720209616896) }, { argument := 33517316302680487822356381696, coefficient := (-33517316302680487822356381696) }, { argument := 58572265697151642760378318848, coefficient := (-58572265697151642760378318848) }, { argument := 53988970571383540264753692672, coefficient := (-53988970571383540264753692672) }, { argument := 1672520773586850689738342400, coefficient := (-1672520773586850689738342400) }, { argument := 53988970571383540264753692672, coefficient := (-53988970571383540264753692672) }, { argument := 36059547878532500870758662144, coefficient := (-36059547878532500870758662144) }, { argument := 1977770711881384747799150592, coefficient := (-1977770711881384747799150592) }, { argument := 33517316302680487822356381696, coefficient := (-33517316302680487822356381696) }, { argument := 1605619942643376662148808704, coefficient := (-1605619942643376662148808704) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 24178516392292583494123520, coefficient := (-24178516392292583494123520) }, { argument := 231728298813530585180405760, coefficient := (-231728298813530585180405760) }, { argument := 2244537238309708180981022720, coefficient := (-2244537238309708180981022720) }, { argument := 231728298813530585180405760, coefficient := (-231728298813530585180405760) }, { argument := 251703672687160740030709760, coefficient := (-251703672687160740030709760) }, { argument := 1910869880937910720209616896, coefficient := (-1910869880937910720209616896) }, { argument := 231728298813530585180405760, coefficient := (-231728298813530585180405760) }, { argument := 205245064663412804016930816, coefficient := (-205245064663412804016930816) }, { argument := 9606793187955225117050535936, coefficient := (-9606793187955225117050535936) }, { argument := 2615219372324130889893150720, coefficient := (-2615219372324130889893150720) }, { argument := 1910870486221700638804279296, coefficient := (-1910870486221700638804279296) }, { argument := 9606793187955225117050535936, coefficient := (-9606793187955225117050535936) }, { argument := 231728298813530585180405760, coefficient := (-231728298813530585180405760) }, { argument := 231728298813530585180405760, coefficient := (-231728298813530585180405760) }, { argument := 198624256125883358726062080, coefficient := (-198624256125883358726062080) }, { argument := 231728298813530585180405760, coefficient := (-231728298813530585180405760) }, { argument := 2615219372324130889893150720, coefficient := (-2615219372324130889893150720) }, { argument := 198624256125883358726062080, coefficient := (-198624256125883358726062080) }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-59459472680038278294554470776832)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    109158805, 44505429, 153, 153, 153, 153,
    87, 87, 87, 87, 44505429, 215541419,
    44505429, 157, 157, 157, 157, 2451,
    2451, 2451, 2451, 2083141209, 10088728999, 2083141209,
    3, 3, 3, 3, 567085305, 2746414855,
    567085305, 347210535, 29071637721, 14535824121, 173600007, 699093,
    1921124985, 1770369415, 1921124985, 1770369415, 828707973, 14535824121,
    25401679917, 23413992147, 725340525, 23413992147, 15638341719, 428860797,
    14535824121, 87040863, 153, 153, 153, 153,
    2083141209, 10088728999, 2083141209, 2529668155, 50803342173, 243353215,
    215541419, 10088728999, 2746414855, 25401679917
  ]
def negativeCoefficients : Array ℕ := #[
    251703067403370821436047360, 205245064663412804016930816, 739862601604153054920179712, 739862601604153054920179712, 739862601604153054920179712, 739862601604153054920179712,
    420706185225890952797749248, 420706185225890952797749248, 420706185225890952797749248, 420706185225890952797749248, 205245064663412804016930816, 1988018696788598674583191552,
    205245064663412804016930816, 759205414717987121715478528, 759205414717987121715478528, 759205414717987121715478528, 759205414717987121715478528, 11852308735501824428819349504,
    11852308735501824428819349504, 11852308735501824428819349504, 11852308735501824428819349504, 9606793187955225117050535936, 93052100936782473445813256192, 9606793187955225117050535936,
    464227514732017603087171584, 464227514732017603087171584, 464227514732017603087171584, 464227514732017603087171584, 2615219372324130889893150720, 25331205975209563756785827840,
    2615219372324130889893150720, 400306492427548303200092160, 33517316302680487822356381696, 33517328432567637790993416192, 400294362540398334563057664, 3301373351608788881378377728,
    8859625232976025310661181440, 8164387878606973943582556160, 8859625232976025310661181440, 8164387878606973943582556160, 1910870486221700638804279296, 33517328432567637790993416192,
    58572286058898335621902761984, 53988990109944278836989394944, 1672521378870640608333004800, 53988990109944278836989394944, 36059560928451011515659583488, 1977771341376526263137599488,
    33517328432567637790993416192, 1605620523715814983999684608, 739862601604153054920179712, 739862601604153054920179712, 739862601604153054920179712, 739862601604153054920179712,
    9606793187955225117050535936, 93052100936782473445813256192, 9606793187955225117050535936, 2916508815418626590145249280, 58572265697151642760378318848, 2244537238309708180981022720,
    1988018696788598674583191552, 93052100936782473445813256192, 25331205975209563756785827840, 58572286058898335621902761984
  ]
def negativeScales : Array ℕ := #[
    26, 25, 7, 7, 7, 7,
    6, 6, 6, 6, 25, 27,
    25, 7, 7, 7, 7, 11,
    11, 11, 11, 30, 33, 30,
    1, 1, 1, 1, 29, 31,
    29, 28, 34, 33, 27, 19,
    30, 30, 30, 30, 29, 33,
    34, 34, 29, 34, 33, 28,
    33, 26, 7, 7, 7, 7,
    30, 33, 30, 31, 35, 27,
    27, 33, 31, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    26701853265293386, 25407477998349906, 7257387842692652, 7257387842692652, 7257387842692652, 7257387842692652,
    6442943495848765, 6442943495848765, 6442943495848765, 6442943495848765, 25407477998349906, 27683389887135756,
    25407477998349906, 7294620748891628, 7294620748891628, 7294620748891628, 7294620748891628, 11259154768866840,
    11259154768866840, 11259154768866840, 11259154768866840, 30956113503583164, 33232025380766896, 30956113503583164,
    1584962500724866, 1584962500724866, 1584962500724866, 1584962500724866, 29078990531027488, 31354902419764618,
    29078990531027488, 28371235481540493, 34758893295660562, 33758893817770531, 27371191765054480, 19415124863820197,
    30839304236645700, 30721403286492548, 30839304236645700, 30721403286492548, 29626288561521882, 33758893817770531,
    34564204860352692, 34446651887580352, 29434083214077281, 34446651887580352, 33864368489328058, 28675934201579233,
    33758893817770531, 26375189525023689, 7257387842692652, 7257387842692652, 7257387842692652, 7257387842692652,
    30956113503583164, 33232025380766896, 30956113503583164, 31236300996796735, 35564204358822053, 27858476595679667,
    27683389887135756, 33232025380766896, 31354902419764618, 34564204860352692
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
noncomputable def negativeCeiling : ℝ := 362044713 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 251703067403370821436047360, coefficient := (-251703067403370821436047360) }, { argument := 205245064663412804016930816, coefficient := (-205245064663412804016930816) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 420706185225890952797749248, coefficient := (-420706185225890952797749248) }, { argument := 420706185225890952797749248, coefficient := (-420706185225890952797749248) }, { argument := 420706185225890952797749248, coefficient := (-420706185225890952797749248) }, { argument := 420706185225890952797749248, coefficient := (-420706185225890952797749248) }, { argument := 205245064663412804016930816, coefficient := (-205245064663412804016930816) }, { argument := 1988018696788598674583191552, coefficient := (-1988018696788598674583191552) }, { argument := 205245064663412804016930816, coefficient := (-205245064663412804016930816) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 759205414717987121715478528, coefficient := (-759205414717987121715478528) }, { argument := 11852308735501824428819349504, coefficient := (-11852308735501824428819349504) }, { argument := 11852308735501824428819349504, coefficient := (-11852308735501824428819349504) }, { argument := 11852308735501824428819349504, coefficient := (-11852308735501824428819349504) }, { argument := 11852308735501824428819349504, coefficient := (-11852308735501824428819349504) }, { argument := 9606793187955225117050535936, coefficient := (-9606793187955225117050535936) }, { argument := 93052100936782473445813256192, coefficient := (-93052100936782473445813256192) }, { argument := 9606793187955225117050535936, coefficient := (-9606793187955225117050535936) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 464227514732017603087171584, coefficient := (-464227514732017603087171584) }, { argument := 2615219372324130889893150720, coefficient := (-2615219372324130889893150720) }, { argument := 25331205975209563756785827840, coefficient := (-25331205975209563756785827840) }, { argument := 2615219372324130889893150720, coefficient := (-2615219372324130889893150720) }, { argument := 400306492427548303200092160, coefficient := (-400306492427548303200092160) }, { argument := 33517316302680487822356381696, coefficient := (-33517316302680487822356381696) }, { argument := 33517328432567637790993416192, coefficient := (-33517328432567637790993416192) }, { argument := 400294362540398334563057664, coefficient := (-400294362540398334563057664) }, { argument := 3301373351608788881378377728, coefficient := (-3301373351608788881378377728) }, { argument := 8859625232976025310661181440, coefficient := (-8859625232976025310661181440) }, { argument := 8164387878606973943582556160, coefficient := (-8164387878606973943582556160) }, { argument := 8859625232976025310661181440, coefficient := (-8859625232976025310661181440) }, { argument := 8164387878606973943582556160, coefficient := (-8164387878606973943582556160) }, { argument := 1910870486221700638804279296, coefficient := (-1910870486221700638804279296) }, { argument := 33517328432567637790993416192, coefficient := (-33517328432567637790993416192) }, { argument := 58572286058898335621902761984, coefficient := (-58572286058898335621902761984) }, { argument := 53988990109944278836989394944, coefficient := (-53988990109944278836989394944) }, { argument := 1672521378870640608333004800, coefficient := (-1672521378870640608333004800) }, { argument := 53988990109944278836989394944, coefficient := (-53988990109944278836989394944) }, { argument := 36059560928451011515659583488, coefficient := (-36059560928451011515659583488) }, { argument := 1977771341376526263137599488, coefficient := (-1977771341376526263137599488) }, { argument := 33517328432567637790993416192, coefficient := (-33517328432567637790993416192) }, { argument := 1605620523715814983999684608, coefficient := (-1605620523715814983999684608) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 739862601604153054920179712, coefficient := (-739862601604153054920179712) }, { argument := 9606793187955225117050535936, coefficient := (-9606793187955225117050535936) }, { argument := 93052100936782473445813256192, coefficient := (-93052100936782473445813256192) }, { argument := 9606793187955225117050535936, coefficient := (-9606793187955225117050535936) }, { argument := 2916508815418626590145249280, coefficient := (-2916508815418626590145249280) }, { argument := 58572265697151642760378318848, coefficient := (-58572265697151642760378318848) }, { argument := 2244537238309708180981022720, coefficient := (-2244537238309708180981022720) }, { argument := 1988018696788598674583191552, coefficient := (-1988018696788598674583191552) }, { argument := 93052100936782473445813256192, coefficient := (-93052100936782473445813256192) }, { argument := 25331205975209563756785827840, coefficient := (-25331205975209563756785827840) }, { argument := 58572286058898335621902761984, coefficient := (-58572286058898335621902761984) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0
