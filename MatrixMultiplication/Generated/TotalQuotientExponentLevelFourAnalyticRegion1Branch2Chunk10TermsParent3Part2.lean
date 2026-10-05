import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 10, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-6331854741920604992403713149632512)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    310256885541, 771, 782689549011, 1423405303085, 782689549011, 4844351174005,
    571607, 4844348865163, 288611, 96321, 5932456965, 22905,
    5932454139, 11565, 13659, 2965915619978643, 283650525, 92559645,
    10128556210145543, 934553835, 1482957782345907, 1872093465, 839008395, 283650525,
    92559645, 291941275146323, 10689, 291939928762285, 5397, 57189583,
    302445228415, 46319, 302445084289, 23387, 96321, 1175,
    11569851, 427259205, 3418072803, 92559645, 45038123349, 81906681515,
    45038123349, 9884935475, 3563, 9884930765, 1799, 42603630195,
    77479293325, 42603630195, 5932456965, 22905, 5932454139, 11565,
    2349, 9884935475, 3563, 9884930765, 1799, 2019,
    57210589119, 104043622465, 57210589119, 152210373035
  ]
def negativeCoefficients : Array ℕ := #[
    1430807341170256105750935896064, 466040903461439546849230848, 902379612485816618508129140736, 3282149167396246487278991441920, 902379612485816618508129140736, 22340626577511160656587936235520,
    10797350952694677166660517888, 22340615929856790498660793188352, 10903415303899929398160130048, 1863119101937611147789977255936, 875476122893205622970929643520, 865326434321033788957655040,
    875475705849215604545386708992, 873826693990199150342307840, 528406968643719036713973055488, 3339324120237037559076442079232, 5232428641048353013392998400, 213428010358551241335767040,
    11403740493453147658036636024832, 4309868854337196034715811840, 3339324057989601938352359079936, 4316753628864891236049223680, 3869243284564703149377454080, 5232428641048353013392998400,
    213428010358551241335767040, 10518292943704381663185064689664, 403819002683149101513572352, 10518244435107166988115252346880, 407785790528759603493076992, 2160561359427933225033761030144,
    1394782431221533233717088092160, 874941172480156386612740096, 1394781766557674141851379040256, 883535879478979140901666816, 1863119101937611147789977255936, 45455610817510056968952217600,
    213426080367952529473929216, 7881541207771604424358625280, 7881539277781005712496787456, 213428010358551241335767040, 51925420936197845855055642624, 188863948979255241103145697280,
    51925420936197845855055642624, 45586218723114390403835494400, 33651583556929091792797696, 45586197002073243610838466560, 33982149210729966957756416, 49118641426133097430458040320,
    178655086872268471313786470400, 49118641426133097430458040320, 875476122893205622970929643520, 865326434321033788957655040, 875475705849215604545386708992, 873826693990199150342307840,
    45436268004396222902156918784, 45586218723114390403835494400, 33651583556929091792797696, 45586197002073243610838466560, 33982149210729966957756416, 39053139676830980859708309504,
    65959318486521587978043654144, 239908259514189090049941831680, 65959318486521587978043654144, 1403892898370253193856973537280
  ]
def negativeScales : Array ℕ := #[
    38, 9, 39, 40, 39, 42,
    19, 42, 18, 16, 32, 14,
    32, 13, 13, 51, 28, 26,
    53, 29, 50, 30, 29, 28,
    26, 48, 13, 48, 12, 25,
    38, 15, 38, 14, 16, 10,
    23, 28, 31, 26, 35, 36,
    35, 33, 11, 33, 10, 35,
    36, 35, 32, 14, 32, 13,
    11, 33, 11, 33, 10, 10,
    35, 36, 35, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    38174672272249169, 9590587049919383, 39509649224947239, 40372483654690192, 39509649224947239, 42139440590516188,
    19124664058476297, 42139439902920352, 18138766761594480, 16555562749717075, 32465982583900928, 14483374942405524,
    32465981896654956, 13497477645523802, 13737564244911302, 51397398977148159, 28079539293349914, 26463879995405919,
    53169278055918831, 29799702532593711, 50397398950255271, 30802005318493961, 29644110005258220, 28079539293349914,
    26463879995405919, 48052671524324079, 13383839268854459, 48052664870841960, 12397941971972645, 25769249050666368,
    38137882943673477, 15499316486274657, 38137882256177377, 14513419189392997, 16555562749717075, 10198445041452363,
    23463866949318620, 28670536333223874, 31670535979944212, 26463879995405919, 35390427663247873, 36253262092991193,
    35390427663247873, 33202584402621439, 11798876768764696, 33202583715202155, 10812979472091290, 35310257314563885,
    36173091744307209, 35310257314563885, 32465982583900928, 14483374942405524, 32465981896654956, 13497477645523802,
    11197830998012197, 33202584402621439, 11798876768764696, 33202583715202155, 10812979472091290, 10979425212320825,
    35735563149460048, 36598397579045289, 35735563149460048, 37147275724653760
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
noncomputable def negativeCeiling : ℝ := 54627999517 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1430807341170256105750935896064, coefficient := (-1430807341170256105750935896064) }, { argument := 466040903461439546849230848, coefficient := (-466040903461439546849230848) }, { argument := 902379612485816618508129140736, coefficient := (-902379612485816618508129140736) }, { argument := 3282149167396246487278991441920, coefficient := (-3282149167396246487278991441920) }, { argument := 902379612485816618508129140736, coefficient := (-902379612485816618508129140736) }, { argument := 22340626577511160656587936235520, coefficient := (-22340626577511160656587936235520) }, { argument := 10797350952694677166660517888, coefficient := (-10797350952694677166660517888) }, { argument := 22340615929856790498660793188352, coefficient := (-22340615929856790498660793188352) }, { argument := 10903415303899929398160130048, coefficient := (-10903415303899929398160130048) }, { argument := 1863119101937611147789977255936, coefficient := (-1863119101937611147789977255936) }, { argument := 875476122893205622970929643520, coefficient := (-875476122893205622970929643520) }, { argument := 865326434321033788957655040, coefficient := (-865326434321033788957655040) }, { argument := 875475705849215604545386708992, coefficient := (-875475705849215604545386708992) }, { argument := 873826693990199150342307840, coefficient := (-873826693990199150342307840) }, { argument := 528406968643719036713973055488, coefficient := (-528406968643719036713973055488) }, { argument := 3339324120237037559076442079232, coefficient := (-3339324120237037559076442079232) }, { argument := 5232428641048353013392998400, coefficient := (-5232428641048353013392998400) }, { argument := 213428010358551241335767040, coefficient := (-213428010358551241335767040) }, { argument := 11403740493453147658036636024832, coefficient := (-11403740493453147658036636024832) }, { argument := 4309868854337196034715811840, coefficient := (-4309868854337196034715811840) }, { argument := 3339324057989601938352359079936, coefficient := (-3339324057989601938352359079936) }, { argument := 4316753628864891236049223680, coefficient := (-4316753628864891236049223680) }, { argument := 3869243284564703149377454080, coefficient := (-3869243284564703149377454080) }, { argument := 5232428641048353013392998400, coefficient := (-5232428641048353013392998400) }, { argument := 213428010358551241335767040, coefficient := (-213428010358551241335767040) }, { argument := 10518292943704381663185064689664, coefficient := (-10518292943704381663185064689664) }, { argument := 403819002683149101513572352, coefficient := (-403819002683149101513572352) }, { argument := 10518244435107166988115252346880, coefficient := (-10518244435107166988115252346880) }, { argument := 407785790528759603493076992, coefficient := (-407785790528759603493076992) }, { argument := 2160561359427933225033761030144, coefficient := (-2160561359427933225033761030144) }, { argument := 1394782431221533233717088092160, coefficient := (-1394782431221533233717088092160) }, { argument := 874941172480156386612740096, coefficient := (-874941172480156386612740096) }, { argument := 1394781766557674141851379040256, coefficient := (-1394781766557674141851379040256) }, { argument := 883535879478979140901666816, coefficient := (-883535879478979140901666816) }, { argument := 1863119101937611147789977255936, coefficient := (-1863119101937611147789977255936) }, { argument := 45455610817510056968952217600, coefficient := (-45455610817510056968952217600) }, { argument := 213426080367952529473929216, coefficient := (-213426080367952529473929216) }, { argument := 7881541207771604424358625280, coefficient := (-7881541207771604424358625280) }, { argument := 7881539277781005712496787456, coefficient := (-7881539277781005712496787456) }, { argument := 213428010358551241335767040, coefficient := (-213428010358551241335767040) }, { argument := 51925420936197845855055642624, coefficient := (-51925420936197845855055642624) }, { argument := 188863948979255241103145697280, coefficient := (-188863948979255241103145697280) }, { argument := 51925420936197845855055642624, coefficient := (-51925420936197845855055642624) }, { argument := 45586218723114390403835494400, coefficient := (-45586218723114390403835494400) }, { argument := 33651583556929091792797696, coefficient := (-33651583556929091792797696) }, { argument := 45586197002073243610838466560, coefficient := (-45586197002073243610838466560) }, { argument := 33982149210729966957756416, coefficient := (-33982149210729966957756416) }, { argument := 49118641426133097430458040320, coefficient := (-49118641426133097430458040320) }, { argument := 178655086872268471313786470400, coefficient := (-178655086872268471313786470400) }, { argument := 49118641426133097430458040320, coefficient := (-49118641426133097430458040320) }, { argument := 875476122893205622970929643520, coefficient := (-875476122893205622970929643520) }, { argument := 865326434321033788957655040, coefficient := (-865326434321033788957655040) }, { argument := 875475705849215604545386708992, coefficient := (-875475705849215604545386708992) }, { argument := 873826693990199150342307840, coefficient := (-873826693990199150342307840) }, { argument := 45436268004396222902156918784, coefficient := (-45436268004396222902156918784) }, { argument := 45586218723114390403835494400, coefficient := (-45586218723114390403835494400) }, { argument := 33651583556929091792797696, coefficient := (-33651583556929091792797696) }, { argument := 45586197002073243610838466560, coefficient := (-45586197002073243610838466560) }, { argument := 33982149210729966957756416, coefficient := (-33982149210729966957756416) }, { argument := 39053139676830980859708309504, coefficient := (-39053139676830980859708309504) }, { argument := 65959318486521587978043654144, coefficient := (-65959318486521587978043654144) }, { argument := 239908259514189090049941831680, coefficient := (-239908259514189090049941831680) }, { argument := 65959318486521587978043654144, coefficient := (-65959318486521587978043654144) }, { argument := 1403892898370253193856973537280, coefficient := (-1403892898370253193856973537280) }] }

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

end TermShard4


end Parent3

namespace Parent3

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 343825905269140752528584433855365120
def positiveArguments : Array ℕ := #[
    10423, 45, 35, 5, 47, 555,
    39, 35, 555, 5, 39, 39,
    39, 39, 39, 45, 47, 5,
    21, 91, 3, 3, 7, 91,
    91, 3, 1123, 45, 21, 91,
    7, 45, 7, 91, 91, 3,
    243, 64433033281, 509, 64432779199, 257, 104471988515,
    2565, 837
  ]
def positiveCoefficients : Array ℕ := #[
    3303180551544708762950034377408512, 1740853180245066011576893440, 1353996917968384675670917120, 1547425049106725343623905280, 1818224432700402278758088704, 21470522556355814142781685760,
    48279661532129830721065844736, 1353996917968384675670917120, 21470522556355814142781685760, 1547425049106725343623905280, 1508739422879057210033307648, 1508739422879057210033307648,
    1508739422879057210033307648, 48279661532129830721065844736, 1508739422879057210033307648, 1740853180245066011576893440, 1818224432700402278758088704, 193428131138340667952988160,
    3249592603124123221610201088, 7040783973435600313488769024, 232113757366008801543585792, 3713820117856140824697372672, 270799383593676935134183424, 7040783973435600313488769024,
    7040783973435600313488769024, 3713820117856140824697372672, 86887916507342628044482281472, 6963412720980264046307573760, 3249592603124123221610201088, 7040783973435600313488769024,
    270799383593676935134183424, 6963412720980264046307573760, 270799383593676935134183424, 7040783973435600313488769024, 7040783973435600313488769024, 232113757366008801543585792,
    19252443490966234035231179931648, 304276396755818766438736725016576, 39381967499766159995228389376, 304275196887498065953541538709504, 39768823762042841331134365696, 493355016961978519007373232701440,
    793829050191750101279063408640, 32379869152558227815330217984
  ]
def positiveScales : Array ℕ := #[
    13, 5, 5, 2, 5, 9,
    5, 5, 9, 2, 5, 5,
    5, 5, 5, 5, 5, 2,
    4, 6, 1, 1, 2, 6,
    6, 1, 10, 5, 4, 6,
    2, 5, 2, 6, 6, 1,
    7, 35, 8, 35, 8, 36,
    11, 9
  ]
def negativeArguments : Array ℕ := #[
    46319, 152210300501, 23387, 2349, 172061063185, 46319,
    172060981231, 23387, 13659, 2019, 15092066532147, 1527,
    15092030391501, 771, 1873713, 2093, 1, 1,
    243, 3841
  ]
def negativeCoefficients : Array ℕ := #[
    874941172480156386612740096, 1403892229362185872632665079808, 883535879478979140901666816, 45436268004396222902156918784, 793491599406015864484648714240, 874941172480156386612740096,
    793491221459899910286500429824, 883535879478979140901666816, 528406968643719036713973055488, 39053139676830980859708309504, 135937250420855925982126669824, 28844214477367792965255168,
    135936924894856208924113108992, 29127556466339971678076928, 70786875757737052338319785984, 40484507847254701802560421888, 158456325028528675187087900672, 158456325028528675187087900672,
    19252443490966234035231179931648, 608630744434578641393604626481152
  ]
def negativeScales : Array ℕ := #[
    15, 37, 14, 11, 37, 15,
    37, 14, 13, 10, 43, 10,
    43, 9, 20, 11, 0, 0,
    7, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13347482960639703, 5491853096329661, 5129283016944966, 2321928094887362, 5554588851677541, 9116343961237468,
    5285402218862248, 5129283016944966, 9116343961237468, 2321928094887362, 5285402218862248, 5285402218862248,
    5285402218862248, 5285402218862248, 5285402218862248, 5491853096329661, 5554588851677541, 2321928094887362,
    4392317422778759, 6507794640198673, 1584962500720924, 1584962500720924, 2807354922011143, 6507794640198673,
    6507794640198673, 1584962500720924, 10133142212400601, 5491853096329661, 4392317422778759, 6507794640198673,
    2807354922011143, 5491853096329661, 2807354922011143, 6507794640198673, 6507794640198673, 1584962500720924,
    7924812503187618, 35907081461942989, 8991521844801183, 35907075772880353, 8005624549193878, 36604325216231931,
    11324743110494416, 9709083812544787
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    15499316486274657, 37147275037154841, 14513419189392997, 11197830998012197, 37324129701247104, 15499316486274657,
    37324129014080261, 14513419189392997, 13737564244911302, 10979425212320825, 43778855599231234, 10576484346799762,
    43778852144436389, 9590587049919383, 20837468560402759, 11031356596255710, 0, 0,
    7924812510375204, 11907266253503503
  ]

abbrev PositiveTerm := Fin 44
abbrev NegativeTerm := Fin 20
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
noncomputable def positiveFloor : ℝ := 506544865559 / 500000000000
noncomputable def negativeCeiling : ℝ := 18135417623 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 874941172480156386612740096, coefficient := (-874941172480156386612740096) }, { argument := 1403892229362185872632665079808, coefficient := (-1403892229362185872632665079808) }, { argument := 883535879478979140901666816, coefficient := (-883535879478979140901666816) }, { argument := 45436268004396222902156918784, coefficient := (-45436268004396222902156918784) }, { argument := 793491599406015864484648714240, coefficient := (-793491599406015864484648714240) }, { argument := 874941172480156386612740096, coefficient := (-874941172480156386612740096) }, { argument := 793491221459899910286500429824, coefficient := (-793491221459899910286500429824) }, { argument := 883535879478979140901666816, coefficient := (-883535879478979140901666816) }, { argument := 528406968643719036713973055488, coefficient := (-528406968643719036713973055488) }, { argument := 39053139676830980859708309504, coefficient := (-39053139676830980859708309504) }, { argument := 135937250420855925982126669824, coefficient := (-135937250420855925982126669824) }, { argument := 28844214477367792965255168, coefficient := (-28844214477367792965255168) }, { argument := 135936924894856208924113108992, coefficient := (-135936924894856208924113108992) }, { argument := 29127556466339971678076928, coefficient := (-29127556466339971678076928) }, { argument := 70786875757737052338319785984, coefficient := (-70786875757737052338319785984) }, { argument := 40484507847254701802560421888, coefficient := (-40484507847254701802560421888) }, { argument := 3303180551544708762950034377408512, coefficient := 3303180551544708762950034377408512 }, { argument := 1740853180245066011576893440, coefficient := 1740853180245066011576893440 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 1547425049106725343623905280, coefficient := 1547425049106725343623905280 }, { argument := 1818224432700402278758088704, coefficient := 1818224432700402278758088704 }, { argument := 21470522556355814142781685760, coefficient := 21470522556355814142781685760 }, { argument := 48279661532129830721065844736, coefficient := 48279661532129830721065844736 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 21470522556355814142781685760, coefficient := 21470522556355814142781685760 }, { argument := 1547425049106725343623905280, coefficient := 1547425049106725343623905280 }, { argument := 1508739422879057210033307648, coefficient := 1508739422879057210033307648 }, { argument := 1508739422879057210033307648, coefficient := 1508739422879057210033307648 }, { argument := 1508739422879057210033307648, coefficient := 1508739422879057210033307648 }, { argument := 48279661532129830721065844736, coefficient := 48279661532129830721065844736 }, { argument := 1508739422879057210033307648, coefficient := 1508739422879057210033307648 }, { argument := 1740853180245066011576893440, coefficient := 1740853180245066011576893440 }, { argument := 1818224432700402278758088704, coefficient := 1818224432700402278758088704 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 3249592603124123221610201088, coefficient := 3249592603124123221610201088 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 270799383593676935134183424, coefficient := 270799383593676935134183424 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 86887916507342628044482281472, coefficient := 86887916507342628044482281472 }, { argument := 6963412720980264046307573760, coefficient := 6963412720980264046307573760 }, { argument := 3249592603124123221610201088, coefficient := 3249592603124123221610201088 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 270799383593676935134183424, coefficient := 270799383593676935134183424 }, { argument := 6963412720980264046307573760, coefficient := 6963412720980264046307573760 }, { argument := 270799383593676935134183424, coefficient := 270799383593676935134183424 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 7040783973435600313488769024, coefficient := 7040783973435600313488769024 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 19252443490966234035231179931648, coefficient := 19252443490966234035231179931648 }, { argument := 19252443490966234035231179931648, coefficient := (-19252443490966234035231179931648) }, { argument := 304276396755818766438736725016576, coefficient := 304276396755818766438736725016576 }, { argument := 39381967499766159995228389376, coefficient := 39381967499766159995228389376 }, { argument := 304275196887498065953541538709504, coefficient := 304275196887498065953541538709504 }, { argument := 39768823762042841331134365696, coefficient := 39768823762042841331134365696 }, { argument := 608630744434578641393604626481152, coefficient := (-608630744434578641393604626481152) }, { argument := 493355016961978519007373232701440, coefficient := 493355016961978519007373232701440 }, { argument := 793829050191750101279063408640, coefficient := 793829050191750101279063408640 }, { argument := 32379869152558227815330217984, coefficient := 32379869152558227815330217984 }] }

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

end TermShard5


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
