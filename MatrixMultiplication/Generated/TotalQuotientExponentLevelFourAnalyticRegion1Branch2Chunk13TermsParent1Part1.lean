import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 13, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13

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
def constantNumerator : ℤ := (-93810119656950929173541110685892608)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    21384327087, 1265455060099626123, 10977332985, 10977332985, 378797838921, 20243649321,
    665644530273, 378797838921, 17426717598777761, 21384327087, 20243649321, 27103370829,
    365177800721116461, 8265, 2697, 629732354401233235, 27231, 365177799018348589,
    54549, 24447, 8265, 2697, 939, 17841,
    27231, 280761, 8451, 27231, 8451, 8451,
    723969, 8451, 280761, 723969, 939, 8451,
    8451, 17841, 45507227675, 85215, 27807, 163282339545,
    280761, 11376803139, 562419, 252057, 85215, 27807,
    33124556967122753, 33124542836762815, 1450301845, 2565, 837, 5246541495,
    8451, 362575341, 16929, 7587, 2565, 837,
    101205914859, 101202807573, 10815219, 20188420387768027
  ]
def negativeCoefficients : Array ℕ := #[
    24654450560148993074540838912, 712387867139848103541115900133376, 25312006523273141532984606720, 25312006523273141532984606720, 436724174390621380248543952896, 23339338633900696157653303296,
    767435893375665060879110504448, 436724174390621380248543952896, 19620739721036597314742978084864, 24654450560148993074540838912, 23339338633900696157653303296, 31248059076088005442985263104,
    205576825906449667404891351416832, 312242871847340941529579520, 12736222404299433141338112, 709015599156134780965560663408640, 257189523390046617628311552, 205576824947876573175184797728768,
    257600369274056276761903104, 230895386813428433078452224, 312242871847340941529579520, 12736222404299433141338112, 283795336154534198762274816, 337006961683509361030201344,
    257189523390046617628311552, 2651712672193928919685005312, 319269753173850973607559168, 257189523390046617628311552, 319269753173850973607559168, 319269753173850973607559168,
    13675387760946616702857117696, 319269753173850973607559168, 2651712672193928919685005312, 13675387760946616702857117696, 283795336154534198762274816, 319269753173850973607559168,
    319269753173850973607559168, 337006961683509361030201344, 209865045606189386802869043200, 3219331678701894535080837120, 131314844789156224457244672, 753006882335789878668353863680,
    2651712672193928919685005312, 209864975882108474199191322624, 2655948634929062991441690624, 2380611057145348327257145344, 3219331678701894535080837120, 131314844789156224457244672,
    18647467801743349691513030311936, 18647459847057880768039910113280, 6688336741085944675701882880, 387611840913940479140167680, 15810482984647572175454208, 24195402057590625282797076480,
    319269753173850973607559168, 6688334522864969812128301056, 319779768754000895290638336, 286628756044255985890492416, 387611840913940479140167680, 15810482984647572175454208,
    233364951268701462642995232768, 233357786355000735060769898496, 102146855420989922876848078848, 5682535158471938172482026995712
  ]
def negativeScales : Array ℕ := #[
    34, 60, 33, 33, 38, 34,
    39, 38, 53, 34, 34, 34,
    58, 13, 11, 59, 14, 58,
    15, 14, 13, 11, 9, 14,
    14, 18, 13, 14, 13, 13,
    19, 13, 18, 19, 9, 13,
    13, 14, 35, 16, 14, 37,
    18, 33, 19, 17, 16, 14,
    54, 54, 30, 11, 9, 32,
    13, 28, 14, 12, 11, 9,
    36, 36, 23, 54
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34315834758682101, 60134361982135759, 33353808533573085, 33353808533573085, 38462637143873457, 34236750336866969,
    39275960993849209, 38462637143873457, 53952150385910788, 34315834758682101, 34236750336866969, 34657753238702325,
    58341376679165794, 13012799104179677, 11397139806235610, 59127516405154646, 14732962342935604, 58341376672438729,
    15735265128813176, 14577369816072640, 13012799104179677, 11397139806235610, 9874981350423323, 14122908861097361,
    14732962342935604, 18098983021851880, 13044906349096087, 14732962342935604, 13044906349096087, 13044906349096087,
    19465568397568892, 13044906349096087, 18098983021851880, 19465568397568892, 9874981350423323, 13044906349096087,
    13044906349096087, 14122908861097361, 35405376648092144, 16378819783250212, 14763160485605156, 37248577802641786,
    18098983021851880, 33405376168781251, 19101285807721301, 17943390504459361, 16378819783250212, 14763160485605156,
    54878750680164432, 54878750064735652, 30433706047305950, 11324743110494417, 9709083812639846, 32288719569678249,
    13044906349096087, 28433705568828706, 14047209134965508, 12889313825985969, 11324743110494417, 9709083812639846,
    36558502652850081, 36558458357663099, 23366559543289984, 54164377551804988
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
noncomputable def negativeCeiling : ℝ := 675854214343 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 24654450560148993074540838912, coefficient := (-24654450560148993074540838912) }, { argument := 712387867139848103541115900133376, coefficient := (-712387867139848103541115900133376) }, { argument := 25312006523273141532984606720, coefficient := (-25312006523273141532984606720) }, { argument := 25312006523273141532984606720, coefficient := (-25312006523273141532984606720) }, { argument := 436724174390621380248543952896, coefficient := (-436724174390621380248543952896) }, { argument := 23339338633900696157653303296, coefficient := (-23339338633900696157653303296) }, { argument := 767435893375665060879110504448, coefficient := (-767435893375665060879110504448) }, { argument := 436724174390621380248543952896, coefficient := (-436724174390621380248543952896) }, { argument := 19620739721036597314742978084864, coefficient := (-19620739721036597314742978084864) }, { argument := 24654450560148993074540838912, coefficient := (-24654450560148993074540838912) }, { argument := 23339338633900696157653303296, coefficient := (-23339338633900696157653303296) }, { argument := 31248059076088005442985263104, coefficient := (-31248059076088005442985263104) }, { argument := 205576825906449667404891351416832, coefficient := (-205576825906449667404891351416832) }, { argument := 312242871847340941529579520, coefficient := (-312242871847340941529579520) }, { argument := 12736222404299433141338112, coefficient := (-12736222404299433141338112) }, { argument := 709015599156134780965560663408640, coefficient := (-709015599156134780965560663408640) }, { argument := 257189523390046617628311552, coefficient := (-257189523390046617628311552) }, { argument := 205576824947876573175184797728768, coefficient := (-205576824947876573175184797728768) }, { argument := 257600369274056276761903104, coefficient := (-257600369274056276761903104) }, { argument := 230895386813428433078452224, coefficient := (-230895386813428433078452224) }, { argument := 312242871847340941529579520, coefficient := (-312242871847340941529579520) }, { argument := 12736222404299433141338112, coefficient := (-12736222404299433141338112) }, { argument := 283795336154534198762274816, coefficient := (-283795336154534198762274816) }, { argument := 337006961683509361030201344, coefficient := (-337006961683509361030201344) }, { argument := 257189523390046617628311552, coefficient := (-257189523390046617628311552) }, { argument := 2651712672193928919685005312, coefficient := (-2651712672193928919685005312) }, { argument := 319269753173850973607559168, coefficient := (-319269753173850973607559168) }, { argument := 257189523390046617628311552, coefficient := (-257189523390046617628311552) }, { argument := 319269753173850973607559168, coefficient := (-319269753173850973607559168) }, { argument := 319269753173850973607559168, coefficient := (-319269753173850973607559168) }, { argument := 13675387760946616702857117696, coefficient := (-13675387760946616702857117696) }, { argument := 319269753173850973607559168, coefficient := (-319269753173850973607559168) }, { argument := 2651712672193928919685005312, coefficient := (-2651712672193928919685005312) }, { argument := 13675387760946616702857117696, coefficient := (-13675387760946616702857117696) }, { argument := 283795336154534198762274816, coefficient := (-283795336154534198762274816) }, { argument := 319269753173850973607559168, coefficient := (-319269753173850973607559168) }, { argument := 319269753173850973607559168, coefficient := (-319269753173850973607559168) }, { argument := 337006961683509361030201344, coefficient := (-337006961683509361030201344) }, { argument := 209865045606189386802869043200, coefficient := (-209865045606189386802869043200) }, { argument := 3219331678701894535080837120, coefficient := (-3219331678701894535080837120) }, { argument := 131314844789156224457244672, coefficient := (-131314844789156224457244672) }, { argument := 753006882335789878668353863680, coefficient := (-753006882335789878668353863680) }, { argument := 2651712672193928919685005312, coefficient := (-2651712672193928919685005312) }, { argument := 209864975882108474199191322624, coefficient := (-209864975882108474199191322624) }, { argument := 2655948634929062991441690624, coefficient := (-2655948634929062991441690624) }, { argument := 2380611057145348327257145344, coefficient := (-2380611057145348327257145344) }, { argument := 3219331678701894535080837120, coefficient := (-3219331678701894535080837120) }, { argument := 131314844789156224457244672, coefficient := (-131314844789156224457244672) }, { argument := 18647467801743349691513030311936, coefficient := (-18647467801743349691513030311936) }, { argument := 18647459847057880768039910113280, coefficient := (-18647459847057880768039910113280) }, { argument := 6688336741085944675701882880, coefficient := (-6688336741085944675701882880) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 24195402057590625282797076480, coefficient := (-24195402057590625282797076480) }, { argument := 319269753173850973607559168, coefficient := (-319269753173850973607559168) }, { argument := 6688334522864969812128301056, coefficient := (-6688334522864969812128301056) }, { argument := 319779768754000895290638336, coefficient := (-319779768754000895290638336) }, { argument := 286628756044255985890492416, coefficient := (-286628756044255985890492416) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 233364951268701462642995232768, coefficient := (-233364951268701462642995232768) }, { argument := 233357786355000735060769898496, coefficient := (-233357786355000735060769898496) }, { argument := 102146855420989922876848078848, coefficient := (-102146855420989922876848078848) }, { argument := 5682535158471938172482026995712, coefficient := (-5682535158471938172482026995712) }] }

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

namespace Parent1

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-96002829014040390345098859663851520)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1876883199, 366931668019240057, 46381803675, 1478125845, 183462364340969991, 758991267,
    758991267, 25774698771, 1398412467, 46381803675, 25774698771, 20202322937067543,
    1478125845, 1398412467, 1876883199, 365170890688158035, 8265, 2697,
    629720647491599453, 27231, 365170888985390579, 54549, 24447, 8265,
    2697, 346211612466916315, 346211523054228517, 744703267, 2565, 837,
    2693217969, 8451, 186175755, 16929, 7587, 2565,
    837, 6276565011, 6276462573, 723411213, 6694228695, 6693989673,
    1065, 1881, 35739, 54549, 562419, 16929,
    54549, 16929, 16929, 1450251, 16929, 562419,
    1450251, 1881, 16929, 16929, 35739, 744703267,
    2565, 837, 2693217969, 8451
  ]
def negativeCoefficients : Array ℕ := #[
    8655596007049568758473424896, 206564165420235508100389387894784, 213898315517441538006397747200, 6816652292862668316742778880, 206560258920625656106166343696384, 7000458828264776985514868736,
    7000458828264776985514868736, 118864817951398278361969065984, 6449039222058450979198599168, 213898315517441538006397747200, 118864817951398278361969065984, 5686448378212238185468639838208,
    6816652292862668316742778880, 6449039222058450979198599168, 8655596007049568758473424896, 205572935903717581757431593041920, 312242871847340941529579520, 12736222404299433141338112,
    709002418347668690794312915484672, 257189523390046617628311552, 205572934945144721714905662619648, 257600369274056276761903104, 230895386813428433078452224, 312242871847340941529579520,
    12736222404299433141338112, 194899811112167860455844641505280, 194899760777299429297432825954304, 6868675288602195948770164736, 387611840913940479140167680, 15810482984647572175454208,
    24840551304429412449572093952, 319269753173850973607559168, 6868673010429302845640540160, 319779768754000895290638336, 286628756044255985890492416, 387611840913940479140167680,
    15810482984647572175454208, 231564376839833953298968215552, 231560597544695107980871335936, 6832425731206547529838935146496, 7717920219221729720213176320, 7717644645617855582435278848,
    20600095966233281136993239040, 284248683336889684702789632, 337545311462556500584562688, 257600369274056276761903104, 2655948634929062991441690624, 319779768754000895290638336,
    257600369274056276761903104, 319779768754000895290638336, 319779768754000895290638336, 13697233428296371681615675392, 319779768754000895290638336, 2655948634929062991441690624,
    13697233428296371681615675392, 284248683336889684702789632, 319779768754000895290638336, 319779768754000895290638336, 337545311462556500584562688, 6868675288602195948770164736,
    387611840913940479140167680, 15810482984647572175454208, 24840551304429412449572093952, 319269753173850973607559168
  ]
def negativeScales : Array ℕ := #[
    30, 58, 35, 30, 57, 29,
    29, 34, 30, 35, 34, 54,
    30, 30, 30, 58, 13, 11,
    59, 14, 58, 15, 14, 13,
    11, 58, 58, 29, 11, 9,
    31, 13, 27, 14, 12, 11,
    9, 32, 32, 29, 32, 32,
    10, 10, 15, 15, 19, 14,
    15, 14, 14, 20, 14, 19,
    20, 10, 14, 14, 15, 29,
    11, 9, 31, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30805691726794681, 58348289034768199, 35432839872833018, 30461121957183877, 57348261750554134, 29499508045097912,
    29499508045097912, 34585236515786985, 30381142805778733, 35432839872833018, 34585236515786985, 54165370707071327,
    30461121957183877, 30381142805778733, 30805691726794681, 58341349379684330, 13012799104179677, 11397139806235610,
    59127489584780329, 14732962342935604, 58341349372957139, 15735265128813176, 14577369816072640, 13012799104179677,
    11397139806235610, 58264431728799142, 58264431356208353, 29472090445740603, 11324743110494417, 9709083812639846,
    31326683849540621, 13044906349096087, 27472089967233592, 14047209134965508, 12889313825985969, 11324743110494417,
    9709083812639846, 32547328082309688, 32547304536309551, 29430240719290729, 32640270692673927, 32640219179344107,
    10056637715113201, 10877284136413052, 15125211646966781, 15735265128813176, 19101285807721301, 14047209134965508,
    15735265128813176, 14047209134965508, 14047209134965508, 20467871183438319, 14047209134965508, 19101285807721301,
    20467871183438319, 10877284136413052, 14047209134965508, 14047209134965508, 15125211646966781, 29472090445740603,
    11324743110494417, 9709083812639846, 31326683849540621, 13044906349096087
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
noncomputable def negativeCeiling : ℝ := 10633168837 / 7812500000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8655596007049568758473424896, coefficient := (-8655596007049568758473424896) }, { argument := 206564165420235508100389387894784, coefficient := (-206564165420235508100389387894784) }, { argument := 213898315517441538006397747200, coefficient := (-213898315517441538006397747200) }, { argument := 6816652292862668316742778880, coefficient := (-6816652292862668316742778880) }, { argument := 206560258920625656106166343696384, coefficient := (-206560258920625656106166343696384) }, { argument := 7000458828264776985514868736, coefficient := (-7000458828264776985514868736) }, { argument := 7000458828264776985514868736, coefficient := (-7000458828264776985514868736) }, { argument := 118864817951398278361969065984, coefficient := (-118864817951398278361969065984) }, { argument := 6449039222058450979198599168, coefficient := (-6449039222058450979198599168) }, { argument := 213898315517441538006397747200, coefficient := (-213898315517441538006397747200) }, { argument := 118864817951398278361969065984, coefficient := (-118864817951398278361969065984) }, { argument := 5686448378212238185468639838208, coefficient := (-5686448378212238185468639838208) }, { argument := 6816652292862668316742778880, coefficient := (-6816652292862668316742778880) }, { argument := 6449039222058450979198599168, coefficient := (-6449039222058450979198599168) }, { argument := 8655596007049568758473424896, coefficient := (-8655596007049568758473424896) }, { argument := 205572935903717581757431593041920, coefficient := (-205572935903717581757431593041920) }, { argument := 312242871847340941529579520, coefficient := (-312242871847340941529579520) }, { argument := 12736222404299433141338112, coefficient := (-12736222404299433141338112) }, { argument := 709002418347668690794312915484672, coefficient := (-709002418347668690794312915484672) }, { argument := 257189523390046617628311552, coefficient := (-257189523390046617628311552) }, { argument := 205572934945144721714905662619648, coefficient := (-205572934945144721714905662619648) }, { argument := 257600369274056276761903104, coefficient := (-257600369274056276761903104) }, { argument := 230895386813428433078452224, coefficient := (-230895386813428433078452224) }, { argument := 312242871847340941529579520, coefficient := (-312242871847340941529579520) }, { argument := 12736222404299433141338112, coefficient := (-12736222404299433141338112) }, { argument := 194899811112167860455844641505280, coefficient := (-194899811112167860455844641505280) }, { argument := 194899760777299429297432825954304, coefficient := (-194899760777299429297432825954304) }, { argument := 6868675288602195948770164736, coefficient := (-6868675288602195948770164736) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 24840551304429412449572093952, coefficient := (-24840551304429412449572093952) }, { argument := 319269753173850973607559168, coefficient := (-319269753173850973607559168) }, { argument := 6868673010429302845640540160, coefficient := (-6868673010429302845640540160) }, { argument := 319779768754000895290638336, coefficient := (-319779768754000895290638336) }, { argument := 286628756044255985890492416, coefficient := (-286628756044255985890492416) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 231564376839833953298968215552, coefficient := (-231564376839833953298968215552) }, { argument := 231560597544695107980871335936, coefficient := (-231560597544695107980871335936) }, { argument := 6832425731206547529838935146496, coefficient := (-6832425731206547529838935146496) }, { argument := 7717920219221729720213176320, coefficient := (-7717920219221729720213176320) }, { argument := 7717644645617855582435278848, coefficient := (-7717644645617855582435278848) }, { argument := 20600095966233281136993239040, coefficient := (-20600095966233281136993239040) }, { argument := 284248683336889684702789632, coefficient := (-284248683336889684702789632) }, { argument := 337545311462556500584562688, coefficient := (-337545311462556500584562688) }, { argument := 257600369274056276761903104, coefficient := (-257600369274056276761903104) }, { argument := 2655948634929062991441690624, coefficient := (-2655948634929062991441690624) }, { argument := 319779768754000895290638336, coefficient := (-319779768754000895290638336) }, { argument := 257600369274056276761903104, coefficient := (-257600369274056276761903104) }, { argument := 319779768754000895290638336, coefficient := (-319779768754000895290638336) }, { argument := 319779768754000895290638336, coefficient := (-319779768754000895290638336) }, { argument := 13697233428296371681615675392, coefficient := (-13697233428296371681615675392) }, { argument := 319779768754000895290638336, coefficient := (-319779768754000895290638336) }, { argument := 2655948634929062991441690624, coefficient := (-2655948634929062991441690624) }, { argument := 13697233428296371681615675392, coefficient := (-13697233428296371681615675392) }, { argument := 284248683336889684702789632, coefficient := (-284248683336889684702789632) }, { argument := 319779768754000895290638336, coefficient := (-319779768754000895290638336) }, { argument := 319779768754000895290638336, coefficient := (-319779768754000895290638336) }, { argument := 337545311462556500584562688, coefficient := (-337545311462556500584562688) }, { argument := 6868675288602195948770164736, coefficient := (-6868675288602195948770164736) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 24840551304429412449572093952, coefficient := (-24840551304429412449572093952) }, { argument := 319269753173850973607559168, coefficient := (-319269753173850973607559168) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13
