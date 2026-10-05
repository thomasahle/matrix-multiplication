import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 0, branch 2,
parent chunk 5, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk5

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 115784339747656501247375208087552
def positiveArguments : Array ℕ := #[
    7, 17, 145, 37, 9, 53,
    9, 145, 37, 53, 2395, 53,
    145, 145, 9, 53
  ]
def positiveCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 657655645870358271040159744, 5609415803011879370636656640, 5725472681694883771408449536, 696341272098026404630757376, 4100676380132822160603348992,
    696341272098026404630757376, 5609415803011879370636656640, 5725472681694883771408449536, 4100676380132822160603348992, 92652074815265179949481328640, 4100676380132822160603348992,
    5609415803011879370636656640, 5609415803011879370636656640, 696341272098026404630757376, 4100676380132822160603348992
  ]
def positiveScales : Array ℕ := #[
    2, 4, 7, 5, 3, 5,
    3, 7, 5, 5, 11, 5,
    7, 7, 3, 5
  ]
def negativeArguments : Array ℕ := #[
    275499245, 6096643, 653175749267, 16679495, 1035279, 6096643,
    1035279, 4256147, 4256147, 14561637373, 1304391281077, 6449309554597,
    51606652052477, 653175749267, 3124797676911, 87979716229419, 24972242148189, 33911005,
    1182436865, 295747365, 16679495, 2104821, 73392633, 18356733,
    1035279, 12395057, 432201061, 108100761, 6096643, 2104821,
    73392633, 18356733, 1035279, 8653153, 301725269, 75466569,
    4256147, 8653153, 301725269, 75466569, 4256147, 29168316497,
    282675290899, 1131011005289, 14561637373, 62849146749, 1769538596721, 502267434151
  ]
def negativeCoefficients : Array ℕ := #[
    635258008126900727437066240, 28115803282443205473206272, 367705257625788215726178304, 38460296942964762203914240, 4774381689471487721865216, 28115803282443205473206272,
    4774381689471487721865216, 39256027224543343490891776, 39256027224543343490891776, 16394946161736772067786752, 367153505462731319397056512, 14522554053440014364029485056,
    14525981184585891236557094912, 367705257625788215726178304, 7036418826672285576150908928, 24764088576685836735677988864, 7029061277074360934527401984, 39096726907330310837370880,
    1363256889498403195836170240, 1363893988157241416440872960, 38460296942964762203914240, 4853386788496176517742592, 169231889730836258793455616, 169310977840209279282315264,
    4774381689471487721865216, 28581055532255261715595264, 996587795081591301783683072, 997053536170121311329189888, 28115803282443205473206272, 4853386788496176517742592,
    169231889730836258793455616, 169310977840209279282315264, 4774381689471487721865216, 39905624705413006923661312, 1391462204453542572301746176, 1392112484463942962987925504,
    39256027224543343490891776, 39905624705413006923661312, 1391462204453542572301746176, 1392112484463942962987925504, 39256027224543343490891776, 16420302413364236400984064,
    636528167379791479624957952, 636702592746433810077319168, 16394946161736772067786752, 141523696939675010048458752, 498080835300650374687358976, 141375714330173671060013056
  ]
def negativeScales : Array ℕ := #[
    28, 22, 39, 23, 19, 22,
    19, 22, 22, 33, 40, 42,
    45, 39, 41, 46, 44, 25,
    30, 28, 23, 21, 26, 24,
    19, 23, 28, 26, 22, 21,
    26, 24, 19, 23, 28, 26,
    22, 23, 28, 26, 22, 34,
    38, 40, 33, 35, 40, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 4087462841250339, 7179909090014934, 5209453365628949, 3169925001442312, 5727920454554652,
    3169925001442312, 7179909090014934, 5209453365628949, 5727920454554652, 11225809940623542, 5727920454554652,
    7179909090014934, 7179909090014934, 3169925001442312, 5727920454554652
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    28037473124224739, 22539583638165363, 39248680272104399, 23991572294302322, 19981588202642544, 22539583638165363,
    19981588202642544, 22021116549230146, 22021116549230146, 33761453536641661, 40246513841494855, 42552281856476054,
    45552622273305424, 39248680272104399, 41506899920434116, 46322236181509479, 44505390593883157, 25015250205491155,
    30139116008389794, 28139790073840235, 23991572294302322, 21005266116918533, 26129131919817172, 24129805985267613,
    19981588202642544, 23563261570041397, 28687127372991373, 26687801438442683, 22539583638165363, 21005266116918533,
    26129131919817172, 24129805985267613, 19981588202642544, 23044794481105170, 28168660284003809, 26169334349454250,
    22021116549230146, 23044794481105170, 28168660284003809, 26169334349454250, 22021116549230146, 34763683070018930,
    38040354824151711, 40040750106171146, 33761453536641661, 35871174109953181, 40686510368500588, 38869664783330798
  ]

abbrev PositiveTerm := Fin 16
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
noncomputable def positiveFloor : ℝ := 53902129 / 1000000000000
noncomputable def negativeCeiling : ℝ := 42004183 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 635258008126900727437066240, coefficient := (-635258008126900727437066240) }, { argument := 28115803282443205473206272, coefficient := (-28115803282443205473206272) }, { argument := 367705257625788215726178304, coefficient := (-367705257625788215726178304) }, { argument := 38460296942964762203914240, coefficient := (-38460296942964762203914240) }, { argument := 4774381689471487721865216, coefficient := (-4774381689471487721865216) }, { argument := 28115803282443205473206272, coefficient := (-28115803282443205473206272) }, { argument := 4774381689471487721865216, coefficient := (-4774381689471487721865216) }, { argument := 39256027224543343490891776, coefficient := (-39256027224543343490891776) }, { argument := 39256027224543343490891776, coefficient := (-39256027224543343490891776) }, { argument := 16394946161736772067786752, coefficient := (-16394946161736772067786752) }, { argument := 367153505462731319397056512, coefficient := (-367153505462731319397056512) }, { argument := 14522554053440014364029485056, coefficient := (-14522554053440014364029485056) }, { argument := 14525981184585891236557094912, coefficient := (-14525981184585891236557094912) }, { argument := 367705257625788215726178304, coefficient := (-367705257625788215726178304) }, { argument := 7036418826672285576150908928, coefficient := (-7036418826672285576150908928) }, { argument := 24764088576685836735677988864, coefficient := (-24764088576685836735677988864) }, { argument := 7029061277074360934527401984, coefficient := (-7029061277074360934527401984) }, { argument := 39096726907330310837370880, coefficient := (-39096726907330310837370880) }, { argument := 1363256889498403195836170240, coefficient := (-1363256889498403195836170240) }, { argument := 1363893988157241416440872960, coefficient := (-1363893988157241416440872960) }, { argument := 38460296942964762203914240, coefficient := (-38460296942964762203914240) }, { argument := 4853386788496176517742592, coefficient := (-4853386788496176517742592) }, { argument := 169231889730836258793455616, coefficient := (-169231889730836258793455616) }, { argument := 169310977840209279282315264, coefficient := (-169310977840209279282315264) }, { argument := 4774381689471487721865216, coefficient := (-4774381689471487721865216) }, { argument := 28581055532255261715595264, coefficient := (-28581055532255261715595264) }, { argument := 996587795081591301783683072, coefficient := (-996587795081591301783683072) }, { argument := 997053536170121311329189888, coefficient := (-997053536170121311329189888) }, { argument := 28115803282443205473206272, coefficient := (-28115803282443205473206272) }, { argument := 4853386788496176517742592, coefficient := (-4853386788496176517742592) }, { argument := 169231889730836258793455616, coefficient := (-169231889730836258793455616) }, { argument := 169310977840209279282315264, coefficient := (-169310977840209279282315264) }, { argument := 4774381689471487721865216, coefficient := (-4774381689471487721865216) }, { argument := 39905624705413006923661312, coefficient := (-39905624705413006923661312) }, { argument := 1391462204453542572301746176, coefficient := (-1391462204453542572301746176) }, { argument := 1392112484463942962987925504, coefficient := (-1392112484463942962987925504) }, { argument := 39256027224543343490891776, coefficient := (-39256027224543343490891776) }, { argument := 39905624705413006923661312, coefficient := (-39905624705413006923661312) }, { argument := 1391462204453542572301746176, coefficient := (-1391462204453542572301746176) }, { argument := 1392112484463942962987925504, coefficient := (-1392112484463942962987925504) }, { argument := 39256027224543343490891776, coefficient := (-39256027224543343490891776) }, { argument := 16420302413364236400984064, coefficient := (-16420302413364236400984064) }, { argument := 636528167379791479624957952, coefficient := (-636528167379791479624957952) }, { argument := 636702592746433810077319168, coefficient := (-636702592746433810077319168) }, { argument := 16394946161736772067786752, coefficient := (-16394946161736772067786752) }, { argument := 141523696939675010048458752, coefficient := (-141523696939675010048458752) }, { argument := 498080835300650374687358976, coefficient := (-498080835300650374687358976) }, { argument := 141375714330173671060013056, coefficient := (-141375714330173671060013056) }, { argument := 1109194275199700726309615304704, coefficient := 1109194275199700726309615304704 }, { argument := 657655645870358271040159744, coefficient := 657655645870358271040159744 }, { argument := 5609415803011879370636656640, coefficient := 5609415803011879370636656640 }, { argument := 5725472681694883771408449536, coefficient := 5725472681694883771408449536 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 4100676380132822160603348992, coefficient := 4100676380132822160603348992 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 5609415803011879370636656640, coefficient := 5609415803011879370636656640 }, { argument := 5725472681694883771408449536, coefficient := 5725472681694883771408449536 }, { argument := 4100676380132822160603348992, coefficient := 4100676380132822160603348992 }, { argument := 92652074815265179949481328640, coefficient := 92652074815265179949481328640 }, { argument := 4100676380132822160603348992, coefficient := 4100676380132822160603348992 }, { argument := 5609415803011879370636656640, coefficient := 5609415803011879370636656640 }, { argument := 5609415803011879370636656640, coefficient := 5609415803011879370636656640 }, { argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 4100676380132822160603348992, coefficient := 4100676380132822160603348992 }] }

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


end Parent3

namespace Parent3

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-63687627073854796395141698420736)
def positiveArguments : Array ℕ := #[
    9, 37, 37, 1, 380031, 10699899,
    3037069, 77881, 49078691, 49091879, 623315, 212907,
    2860563, 36014029, 5712959, 105515, 81777, 4112901,
    8222481, 165379
  ]
def positiveCoefficients : Array ℕ := #[
    696341272098026404630757376, 5725472681694883771408449536, 5725472681694883771408449536, 618970019642690137449562112, 28714330509622946243297673216, 101057688815380867904761233408,
    28684305703524861039028994048, 11769043969675866844411461632, 463535130803032221445229903872, 463659687941384391207386349568, 11774087457079571625499688960, 2010849761536655107024748544,
    54034507333348163685703483392, 680285773850781623783035764736, 53957372199216970900782972928, 1993121997759962458892533760, 1544723855478523906561671168, 77690503319044186676221968384,
    77659137360864966492712599552, 1561960493140998111591661568
  ]
def positiveScales : Array ℕ := #[
    3, 5, 5, 0, 18, 23,
    21, 16, 25, 25, 19, 17,
    21, 25, 22, 16, 16, 21,
    22, 17
  ]
def negativeArguments : Array ℕ := #[
    1, 1, 3, 5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 158456325028528675187087900672, 950737950171172051122527404032, 792281625142643375935439503360, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 0, 1, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 5209453365628949, 5209453365628949, 0, 18535757581735393, 23351093842811150,
    21534248255184453, 16248983788078363, 25548593434952440, 25548981051369736, 19249601905884829, 17699863858225676,
    21447867687437197, 25102055671492295, 22445806745542386, 16687088581302838, 16319407517927179, 21971724914119468,
    22971142337783268, 17335416525636905
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0, 1584962500724866, 2321928094887363, 0
  ]

abbrev PositiveTerm := Fin 20
abbrev NegativeTerm := Fin 5
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
noncomputable def positiveFloor : ℝ := 610722659 / 1000000000000
noncomputable def negativeCeiling : ℝ := 40282089 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 696341272098026404630757376, coefficient := 696341272098026404630757376 }, { argument := 5725472681694883771408449536, coefficient := 5725472681694883771408449536 }, { argument := 5725472681694883771408449536, coefficient := 5725472681694883771408449536 }, { argument := 618970019642690137449562112, coefficient := 618970019642690137449562112 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 28714330509622946243297673216, coefficient := 28714330509622946243297673216 }, { argument := 101057688815380867904761233408, coefficient := 101057688815380867904761233408 }, { argument := 28684305703524861039028994048, coefficient := 28684305703524861039028994048 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 11769043969675866844411461632, coefficient := 11769043969675866844411461632 }, { argument := 463535130803032221445229903872, coefficient := 463535130803032221445229903872 }, { argument := 463659687941384391207386349568, coefficient := 463659687941384391207386349568 }, { argument := 11774087457079571625499688960, coefficient := 11774087457079571625499688960 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 2010849761536655107024748544, coefficient := 2010849761536655107024748544 }, { argument := 54034507333348163685703483392, coefficient := 54034507333348163685703483392 }, { argument := 680285773850781623783035764736, coefficient := 680285773850781623783035764736 }, { argument := 53957372199216970900782972928, coefficient := 53957372199216970900782972928 }, { argument := 1993121997759962458892533760, coefficient := 1993121997759962458892533760 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 1544723855478523906561671168, coefficient := 1544723855478523906561671168 }, { argument := 77690503319044186676221968384, coefficient := 77690503319044186676221968384 }, { argument := 77659137360864966492712599552, coefficient := 77659137360864966492712599552 }, { argument := 1561960493140998111591661568, coefficient := 1561960493140998111591661568 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk5
