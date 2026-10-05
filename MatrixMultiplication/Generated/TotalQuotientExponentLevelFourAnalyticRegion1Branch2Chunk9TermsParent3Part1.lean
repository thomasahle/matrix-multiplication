import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 9, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9

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
def constantNumerator : ℤ := (-2608456217349657540803419208417280)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1701, 6615, 5859, 274239, 74655, 1701,
    274239, 6615, 6615, 2835, 6615, 74655,
    2835, 6615, 5859, 6239793776549, 1896507856036217, 25389,
    77663502393433045, 837, 1953, 25389, 25389, 837,
    313317, 12555, 1896507860569977, 25389, 1953, 12555,
    1953, 25389, 25389, 49934827103035, 15435, 3969,
    15435, 13671, 639891, 174195, 3969, 639891,
    15435, 15435, 6615, 15435, 174195, 6615,
    15435, 13671, 21371495, 1751637365, 98735, 17881590615,
    3255, 7595, 98735, 98735, 3255, 1218455,
    48825, 875819315, 98735, 7595
  ]
def negativeCoefficients : Array ℕ := #[
    1028191409582242113087602688, 999630537093846498835169280, 885387047140264041825435648, 41441825980662036280280875008, 11281544632916267629711196160, 1028191409582242113087602688,
    41441825980662036280280875008, 999630537093846498835169280, 999630537093846498835169280, 856826174651868427573002240, 999630537093846498835169280, 11281544632916267629711196160,
    856826174651868427573002240, 999630537093846498835169280, 885387047140264041825435648, 28101532926934816382259298304, 4270556036874962577160526626816, 1918338602137238757288443904,
    43720665054919085711778948055040, 1011870911017444619229069312, 73782253928355336818786304, 1918338602137238757288443904, 1918338602137238757288443904, 1011870911017444619229069312,
    23673563189012298070713434112, 1897257958157708661054504960, 4270556047084082500454156599296, 1918338602137238757288443904, 73782253928355336818786304, 1897257958157708661054504960,
    73782253928355336818786304, 1918338602137238757288443904, 1918338602137238757288443904, 28110808591754821283788881920, 72889726663092973873397760, 74972290282038487412637696,
    72889726663092973873397760, 64559472187310919716438016, 3021799811089940145437147136, 822612629483477847999774720, 74972290282038487412637696, 3021799811089940145437147136,
    72889726663092973873397760, 72889726663092973873397760, 62476908568365406177198080, 72889726663092973873397760, 822612629483477847999774720, 62476908568365406177198080,
    72889726663092973873397760, 64559472187310919716438016, 197117249368781656906792960, 16156003091050982383990865920, 1865051418744537680697098240, 164928562852875793206261841920,
    983763385711404490917150720, 71732746874789910796042240, 1865051418744537680697098240, 1865051418744537680697098240, 983763385711404490917150720, 23015964211539734235415838720,
    1844556348208883420469657600, 16156014758616609005282263040, 1865051418744537680697098240, 71732746874789910796042240
  ]
def negativeScales : Array ℕ := #[
    10, 12, 12, 18, 16, 10,
    18, 12, 12, 11, 12, 16,
    11, 12, 12, 42, 50, 14,
    56, 9, 10, 14, 14, 9,
    18, 13, 50, 14, 10, 13,
    10, 14, 14, 45, 13, 11,
    13, 13, 19, 17, 11, 19,
    13, 13, 12, 13, 17, 12,
    13, 13, 24, 30, 16, 34,
    11, 12, 16, 16, 11, 20,
    15, 29, 16, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    10732167425814919, 12691525441225267, 12516438734608414, 18065074228287818, 16187951267285539, 10732167425814919,
    18065074228287818, 12691525441225267, 12691525441225267, 11469133019829685, 12691525441225267, 16187951267285539,
    11469133019829685, 12691525441225267, 12516438734608414, 42504635487853744, 50752266771367119, 14631915952041241,
    56108086288175328, 9709083812639846, 10931476241484805, 14631915952041241, 14631915952041241, 9709083812639846,
    18257263524229789, 13615974408167608, 50752266774816001, 14631915952041241, 10931476241484805, 13615974408167608,
    10931476241484805, 14631915952041241, 14631915952041241, 45505111609481017, 13913917868096136, 11954559858255908,
    13913917868096136, 13738831156120225, 19287466649624266, 17410343688621996, 11954559858255908, 19287466649624266,
    13913917868096136, 13913917868096136, 12691525441225267, 13913917868096136, 17410343688621996, 12691525441225267,
    13913917868096136, 13738831156120225, 24349184496572671, 30706056984107187, 16591273967534972, 34057756022660313,
    11668441828086828, 12890834253091783, 16591273967534972, 16591273967534972, 11668441828086828, 20216621539732443,
    15575332423664331, 29706058025994399, 16591273967534972, 12890834253091783
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
noncomputable def negativeCeiling : ℝ := 6979325741 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1028191409582242113087602688, coefficient := (-1028191409582242113087602688) }, { argument := 999630537093846498835169280, coefficient := (-999630537093846498835169280) }, { argument := 885387047140264041825435648, coefficient := (-885387047140264041825435648) }, { argument := 41441825980662036280280875008, coefficient := (-41441825980662036280280875008) }, { argument := 11281544632916267629711196160, coefficient := (-11281544632916267629711196160) }, { argument := 1028191409582242113087602688, coefficient := (-1028191409582242113087602688) }, { argument := 41441825980662036280280875008, coefficient := (-41441825980662036280280875008) }, { argument := 999630537093846498835169280, coefficient := (-999630537093846498835169280) }, { argument := 999630537093846498835169280, coefficient := (-999630537093846498835169280) }, { argument := 856826174651868427573002240, coefficient := (-856826174651868427573002240) }, { argument := 999630537093846498835169280, coefficient := (-999630537093846498835169280) }, { argument := 11281544632916267629711196160, coefficient := (-11281544632916267629711196160) }, { argument := 856826174651868427573002240, coefficient := (-856826174651868427573002240) }, { argument := 999630537093846498835169280, coefficient := (-999630537093846498835169280) }, { argument := 885387047140264041825435648, coefficient := (-885387047140264041825435648) }, { argument := 28101532926934816382259298304, coefficient := (-28101532926934816382259298304) }, { argument := 4270556036874962577160526626816, coefficient := (-4270556036874962577160526626816) }, { argument := 1918338602137238757288443904, coefficient := (-1918338602137238757288443904) }, { argument := 43720665054919085711778948055040, coefficient := (-43720665054919085711778948055040) }, { argument := 1011870911017444619229069312, coefficient := (-1011870911017444619229069312) }, { argument := 73782253928355336818786304, coefficient := (-73782253928355336818786304) }, { argument := 1918338602137238757288443904, coefficient := (-1918338602137238757288443904) }, { argument := 1918338602137238757288443904, coefficient := (-1918338602137238757288443904) }, { argument := 1011870911017444619229069312, coefficient := (-1011870911017444619229069312) }, { argument := 23673563189012298070713434112, coefficient := (-23673563189012298070713434112) }, { argument := 1897257958157708661054504960, coefficient := (-1897257958157708661054504960) }, { argument := 4270556047084082500454156599296, coefficient := (-4270556047084082500454156599296) }, { argument := 1918338602137238757288443904, coefficient := (-1918338602137238757288443904) }, { argument := 73782253928355336818786304, coefficient := (-73782253928355336818786304) }, { argument := 1897257958157708661054504960, coefficient := (-1897257958157708661054504960) }, { argument := 73782253928355336818786304, coefficient := (-73782253928355336818786304) }, { argument := 1918338602137238757288443904, coefficient := (-1918338602137238757288443904) }, { argument := 1918338602137238757288443904, coefficient := (-1918338602137238757288443904) }, { argument := 28110808591754821283788881920, coefficient := (-28110808591754821283788881920) }, { argument := 72889726663092973873397760, coefficient := (-72889726663092973873397760) }, { argument := 74972290282038487412637696, coefficient := (-74972290282038487412637696) }, { argument := 72889726663092973873397760, coefficient := (-72889726663092973873397760) }, { argument := 64559472187310919716438016, coefficient := (-64559472187310919716438016) }, { argument := 3021799811089940145437147136, coefficient := (-3021799811089940145437147136) }, { argument := 822612629483477847999774720, coefficient := (-822612629483477847999774720) }, { argument := 74972290282038487412637696, coefficient := (-74972290282038487412637696) }, { argument := 3021799811089940145437147136, coefficient := (-3021799811089940145437147136) }, { argument := 72889726663092973873397760, coefficient := (-72889726663092973873397760) }, { argument := 72889726663092973873397760, coefficient := (-72889726663092973873397760) }, { argument := 62476908568365406177198080, coefficient := (-62476908568365406177198080) }, { argument := 72889726663092973873397760, coefficient := (-72889726663092973873397760) }, { argument := 822612629483477847999774720, coefficient := (-822612629483477847999774720) }, { argument := 62476908568365406177198080, coefficient := (-62476908568365406177198080) }, { argument := 72889726663092973873397760, coefficient := (-72889726663092973873397760) }, { argument := 64559472187310919716438016, coefficient := (-64559472187310919716438016) }, { argument := 197117249368781656906792960, coefficient := (-197117249368781656906792960) }, { argument := 16156003091050982383990865920, coefficient := (-16156003091050982383990865920) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 164928562852875793206261841920, coefficient := (-164928562852875793206261841920) }, { argument := 983763385711404490917150720, coefficient := (-983763385711404490917150720) }, { argument := 71732746874789910796042240, coefficient := (-71732746874789910796042240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 983763385711404490917150720, coefficient := (-983763385711404490917150720) }, { argument := 23015964211539734235415838720, coefficient := (-23015964211539734235415838720) }, { argument := 1844556348208883420469657600, coefficient := (-1844556348208883420469657600) }, { argument := 16156014758616609005282263040, coefficient := (-16156014758616609005282263040) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 71732746874789910796042240, coefficient := (-71732746874789910796042240) }] }

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
def constantNumerator : ℤ := (-87463842716013685080539483078656)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    48825, 7595, 98735, 98735, 22482535, 2115778966579,
    79304492780493, 158597897638315, 4242645855829, 200655, 51597, 200655,
    177723, 8318583, 2264535, 51597, 8318583, 200655,
    200655, 85995, 200655, 2264535, 85995, 200655,
    177723, 200655, 51597, 200655, 177723, 8318583,
    2264535, 51597, 8318583, 200655, 200655, 85995,
    200655, 2264535, 85995, 200655, 177723, 188035733,
    16249405055, 87451, 168071524197, 2883, 6727, 87451,
    87451, 2883, 1079203, 43245, 8124708473, 87451,
    6727, 43245, 6727, 87451, 87451, 195908245,
    6615, 1701, 6615, 5859
  ]
def negativeCoefficients : Array ℕ := #[
    1844556348208883420469657600, 71732746874789910796042240, 1865051418744537680697098240, 1865051418744537680697098240, 207364784636608787020513280, 9528621365483517510034653184,
    357155684135034465033312534528, 357130716352829750795955077120, 9553589147688231747392110592, 1895132893240417320708341760, 1949279547333000672728580096, 1895132893240417320708341760,
    1678546276870083912627388416, 78566795088338443781365825536, 21387928366570424047994142720, 1949279547333000672728580096, 78566795088338443781365825536, 1895132893240417320708341760,
    1895132893240417320708341760, 1624399622777500560607150080, 1895132893240417320708341760, 21387928366570424047994142720, 1624399622777500560607150080, 1895132893240417320708341760,
    1678546276870083912627388416, 1895132893240417320708341760, 1949279547333000672728580096, 1895132893240417320708341760, 1678546276870083912627388416, 78566795088338443781365825536,
    21387928366570424047994142720, 1949279547333000672728580096, 78566795088338443781365825536, 1895132893240417320708341760, 1895132893240417320708341760, 1624399622777500560607150080,
    1895132893240417320708341760, 21387928366570424047994142720, 1624399622777500560607150080, 1895132893240417320708341760, 1678546276870083912627388416, 216790440210211347950993408,
    18734288524976705039425863680, 1651902685173733374331715584, 193773274558771328498660278272, 871333284487243977669476352, 63534718660528206705065984, 1651902685173733374331715584,
    1651902685173733374331715584, 871333284487243977669476352, 20385568301649478894225457152, 1633749908413582458130268160, 18734302234366316319443255296, 1651902685173733374331715584,
    63534718660528206705065984, 1633749908413582458130268160, 63534718660528206705065984, 1651902685173733374331715584, 1651902685173733374331715584, 225866828590286806051717120,
    999630537093846498835169280, 1028191409582242113087602688, 999630537093846498835169280, 885387047140264041825435648
  ]
def negativeScales : Array ℕ := #[
    15, 12, 16, 16, 24, 40,
    46, 47, 41, 17, 15, 17,
    17, 22, 21, 15, 22, 17,
    17, 16, 17, 21, 16, 17,
    17, 17, 15, 17, 17, 22,
    21, 15, 22, 17, 17, 16,
    17, 21, 16, 17, 17, 27,
    33, 16, 37, 11, 12, 16,
    16, 11, 20, 15, 32, 16,
    12, 15, 12, 16, 16, 27,
    12, 10, 12, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15575332423664331, 12890834253091783, 16591273967534972, 16591273967534972, 24422301378851210, 40944326066459053,
    46172467833746575, 47172366975335835, 41948101407064790, 17614357580651952, 15654999565165109, 17614357580651952,
    17439270874085520, 22987906387263822, 21110783406763079, 15654999565165109, 22987906387263822, 17614357580651952,
    17614357580651952, 16391965159307136, 17614357580651952, 21110783406763079, 16391965159307136, 17614357580651952,
    17439270874085520, 17614357580651952, 15654999565165109, 17614357580651952, 17439270874085520, 22987906387263822,
    21110783406763079, 15654999565165109, 22987906387263822, 17614357580651952, 17614357580651952, 16391965159307136,
    17614357580651952, 21110783406763079, 16391965159307136, 17614357580651952, 17439270874085520, 27486431606764277,
    33919667852285080, 16416187260972460, 37290284357985500, 11493355121495124, 12715747542935743, 16416187260972460,
    16416187260972460, 11493355121495124, 20041534833174352, 15400245717103432, 32919668908021106, 16416187260972460,
    12715747542935743, 15400245717103432, 12715747542935743, 16416187260972460, 16416187260972460, 27545602875288010,
    12691525441225267, 10732167425814919, 12691525441225267, 12516438734608414
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
noncomputable def negativeCeiling : ℝ := 640171551 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1844556348208883420469657600, coefficient := (-1844556348208883420469657600) }, { argument := 71732746874789910796042240, coefficient := (-71732746874789910796042240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 207364784636608787020513280, coefficient := (-207364784636608787020513280) }, { argument := 9528621365483517510034653184, coefficient := (-9528621365483517510034653184) }, { argument := 357155684135034465033312534528, coefficient := (-357155684135034465033312534528) }, { argument := 357130716352829750795955077120, coefficient := (-357130716352829750795955077120) }, { argument := 9553589147688231747392110592, coefficient := (-9553589147688231747392110592) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1949279547333000672728580096, coefficient := (-1949279547333000672728580096) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1678546276870083912627388416, coefficient := (-1678546276870083912627388416) }, { argument := 78566795088338443781365825536, coefficient := (-78566795088338443781365825536) }, { argument := 21387928366570424047994142720, coefficient := (-21387928366570424047994142720) }, { argument := 1949279547333000672728580096, coefficient := (-1949279547333000672728580096) }, { argument := 78566795088338443781365825536, coefficient := (-78566795088338443781365825536) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1624399622777500560607150080, coefficient := (-1624399622777500560607150080) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 21387928366570424047994142720, coefficient := (-21387928366570424047994142720) }, { argument := 1624399622777500560607150080, coefficient := (-1624399622777500560607150080) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1678546276870083912627388416, coefficient := (-1678546276870083912627388416) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1949279547333000672728580096, coefficient := (-1949279547333000672728580096) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1678546276870083912627388416, coefficient := (-1678546276870083912627388416) }, { argument := 78566795088338443781365825536, coefficient := (-78566795088338443781365825536) }, { argument := 21387928366570424047994142720, coefficient := (-21387928366570424047994142720) }, { argument := 1949279547333000672728580096, coefficient := (-1949279547333000672728580096) }, { argument := 78566795088338443781365825536, coefficient := (-78566795088338443781365825536) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1624399622777500560607150080, coefficient := (-1624399622777500560607150080) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 21387928366570424047994142720, coefficient := (-21387928366570424047994142720) }, { argument := 1624399622777500560607150080, coefficient := (-1624399622777500560607150080) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1678546276870083912627388416, coefficient := (-1678546276870083912627388416) }, { argument := 216790440210211347950993408, coefficient := (-216790440210211347950993408) }, { argument := 18734288524976705039425863680, coefficient := (-18734288524976705039425863680) }, { argument := 1651902685173733374331715584, coefficient := (-1651902685173733374331715584) }, { argument := 193773274558771328498660278272, coefficient := (-193773274558771328498660278272) }, { argument := 871333284487243977669476352, coefficient := (-871333284487243977669476352) }, { argument := 63534718660528206705065984, coefficient := (-63534718660528206705065984) }, { argument := 1651902685173733374331715584, coefficient := (-1651902685173733374331715584) }, { argument := 1651902685173733374331715584, coefficient := (-1651902685173733374331715584) }, { argument := 871333284487243977669476352, coefficient := (-871333284487243977669476352) }, { argument := 20385568301649478894225457152, coefficient := (-20385568301649478894225457152) }, { argument := 1633749908413582458130268160, coefficient := (-1633749908413582458130268160) }, { argument := 18734302234366316319443255296, coefficient := (-18734302234366316319443255296) }, { argument := 1651902685173733374331715584, coefficient := (-1651902685173733374331715584) }, { argument := 63534718660528206705065984, coefficient := (-63534718660528206705065984) }, { argument := 1633749908413582458130268160, coefficient := (-1633749908413582458130268160) }, { argument := 63534718660528206705065984, coefficient := (-63534718660528206705065984) }, { argument := 1651902685173733374331715584, coefficient := (-1651902685173733374331715584) }, { argument := 1651902685173733374331715584, coefficient := (-1651902685173733374331715584) }, { argument := 225866828590286806051717120, coefficient := (-225866828590286806051717120) }, { argument := 999630537093846498835169280, coefficient := (-999630537093846498835169280) }, { argument := 1028191409582242113087602688, coefficient := (-1028191409582242113087602688) }, { argument := 999630537093846498835169280, coefficient := (-999630537093846498835169280) }, { argument := 885387047140264041825435648, coefficient := (-885387047140264041825435648) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9
