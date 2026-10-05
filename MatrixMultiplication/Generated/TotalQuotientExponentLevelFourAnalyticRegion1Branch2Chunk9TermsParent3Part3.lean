import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
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

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-814051999055528338642618917322752)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    25389, 25389, 24967413505747, 200655, 51597, 200655,
    177723, 8318583, 2264535, 51597, 8318583, 200655,
    200655, 85995, 200655, 2264535, 85995, 200655,
    177723, 3598030505, 215025096123, 4093271, 1986327511737, 134943,
    314867, 4093271, 4093271, 134943, 50513663, 2024145,
    107512618269, 4093271, 314867, 2024145, 314867, 4093271,
    4093271, 3966514857, 11245213448141, 420595991578675, 841138288549717, 22544121503915,
    21371495, 1751637365, 98735, 17881590615, 3255, 7595,
    98735, 98735, 3255, 1218455, 48825, 875819315,
    98735, 7595, 48825, 7595, 98735, 98735,
    22482535, 949091895, 34618081737, 276944697147
  ]
def negativeCoefficients : Array ℕ := #[
    1918338602137238757288443904, 1918338602137238757288443904, 28110808540221819597648560128, 1895132893240417320708341760, 1949279547333000672728580096, 1895132893240417320708341760,
    1678546276870083912627388416, 78566795088338443781365825536, 21387928366570424047994142720, 1949279547333000672728580096, 78566795088338443781365825536, 1895132893240417320708341760,
    1895132893240417320708341760, 1624399622777500560607150080, 1895132893240417320708341760, 21387928366570424047994142720, 1624399622777500560607150080, 1895132893240417320708341760,
    1678546276870083912627388416, 4148246743445933451515002880, 247907057350361058338351874048, 77319703102809262134042558464, 2290079703473796536291202957312, 40784019219064226180593876992,
    2973834734723433159001636864, 77319703102809262134042558464, 77319703102809262134042558464, 40784019219064226180593876992, 954176116312690125016810913792, 76470036035745424088613519360,
    247907219237834127708770009088, 77319703102809262134042558464, 2973834734723433159001636864, 76470036035745424088613519360, 2973834734723433159001636864, 77319703102809262134042558464,
    77319703102809262134042558464, 4573080276977852474229522432, 101287878189498996090178895872, 3788391901894490007300315545600, 3788150082879562223510074949632, 101529697204426779880419491840,
    197117249368781656906792960, 16156003091050982383990865920, 1865051418744537680697098240, 164928562852875793206261841920, 983763385711404490917150720, 71732746874789910796042240,
    1865051418744537680697098240, 1865051418744537680697098240, 983763385711404490917150720, 23015964211539734235415838720, 1844556348208883420469657600, 16156014758616609005282263040,
    1865051418744537680697098240, 71732746874789910796042240, 1844556348208883420469657600, 71732746874789910796042240, 1865051418744537680697098240, 1865051418744537680697098240,
    207364784636608787020513280, 17507655289497018022829752320, 638590894125197610640308436992, 638590993855213602141785554944
  ]
def negativeScales : Array ℕ := #[
    14, 14, 44, 17, 15, 17,
    17, 22, 21, 15, 22, 17,
    17, 16, 17, 21, 16, 17,
    17, 31, 37, 21, 40, 17,
    18, 21, 21, 17, 25, 20,
    36, 21, 18, 20, 18, 21,
    21, 31, 43, 48, 49, 44,
    24, 30, 16, 34, 11, 12,
    16, 16, 11, 20, 15, 29,
    16, 12, 15, 12, 16, 16,
    24, 29, 35, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    14631915952041241, 14631915952041241, 44505111606836255, 17614357580651952, 15654999565165109, 17614357580651952,
    17439270874085520, 22987906387263822, 21110783406763079, 15654999565165109, 22987906387263822, 17614357580651952,
    17614357580651952, 16391965159307136, 17614357580651952, 21110783406763079, 16391965159307136, 17614357580651952,
    17439270874085520, 31744560272355466, 37645714094010008, 21964822768012238, 40853240658927583, 17041990615174776,
    18264383036511224, 21964822768012238, 21964822768012238, 17041990615174776, 25590170326858519, 20948881221012139,
    36645715036113798, 21964822768012238, 18264383036511224, 20948881221012139, 18264383036511224, 21964822768012238,
    21964822768012238, 31885224810093250, 43354376279058017, 48579428429192262, 49579336336758938, 44357816525873580,
    24349184496572671, 30706056984107187, 16591273967534972, 34057756022660313, 11668441828086828, 12890834253091783,
    16591273967534972, 16591273967534972, 11668441828086828, 20216621539732443, 15575332423664331, 29706058025994399,
    16591273967534972, 12890834253091783, 15575332423664331, 12890834253091783, 16591273967534972, 16591273967534972,
    24422301378851210, 29821972541809538, 35010806732931396, 38010806958239945
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
noncomputable def negativeCeiling : ℝ := 7138566829 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1918338602137238757288443904, coefficient := (-1918338602137238757288443904) }, { argument := 1918338602137238757288443904, coefficient := (-1918338602137238757288443904) }, { argument := 28110808540221819597648560128, coefficient := (-28110808540221819597648560128) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1949279547333000672728580096, coefficient := (-1949279547333000672728580096) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1678546276870083912627388416, coefficient := (-1678546276870083912627388416) }, { argument := 78566795088338443781365825536, coefficient := (-78566795088338443781365825536) }, { argument := 21387928366570424047994142720, coefficient := (-21387928366570424047994142720) }, { argument := 1949279547333000672728580096, coefficient := (-1949279547333000672728580096) }, { argument := 78566795088338443781365825536, coefficient := (-78566795088338443781365825536) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1624399622777500560607150080, coefficient := (-1624399622777500560607150080) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 21387928366570424047994142720, coefficient := (-21387928366570424047994142720) }, { argument := 1624399622777500560607150080, coefficient := (-1624399622777500560607150080) }, { argument := 1895132893240417320708341760, coefficient := (-1895132893240417320708341760) }, { argument := 1678546276870083912627388416, coefficient := (-1678546276870083912627388416) }, { argument := 4148246743445933451515002880, coefficient := (-4148246743445933451515002880) }, { argument := 247907057350361058338351874048, coefficient := (-247907057350361058338351874048) }, { argument := 77319703102809262134042558464, coefficient := (-77319703102809262134042558464) }, { argument := 2290079703473796536291202957312, coefficient := (-2290079703473796536291202957312) }, { argument := 40784019219064226180593876992, coefficient := (-40784019219064226180593876992) }, { argument := 2973834734723433159001636864, coefficient := (-2973834734723433159001636864) }, { argument := 77319703102809262134042558464, coefficient := (-77319703102809262134042558464) }, { argument := 77319703102809262134042558464, coefficient := (-77319703102809262134042558464) }, { argument := 40784019219064226180593876992, coefficient := (-40784019219064226180593876992) }, { argument := 954176116312690125016810913792, coefficient := (-954176116312690125016810913792) }, { argument := 76470036035745424088613519360, coefficient := (-76470036035745424088613519360) }, { argument := 247907219237834127708770009088, coefficient := (-247907219237834127708770009088) }, { argument := 77319703102809262134042558464, coefficient := (-77319703102809262134042558464) }, { argument := 2973834734723433159001636864, coefficient := (-2973834734723433159001636864) }, { argument := 76470036035745424088613519360, coefficient := (-76470036035745424088613519360) }, { argument := 2973834734723433159001636864, coefficient := (-2973834734723433159001636864) }, { argument := 77319703102809262134042558464, coefficient := (-77319703102809262134042558464) }, { argument := 77319703102809262134042558464, coefficient := (-77319703102809262134042558464) }, { argument := 4573080276977852474229522432, coefficient := (-4573080276977852474229522432) }, { argument := 101287878189498996090178895872, coefficient := (-101287878189498996090178895872) }, { argument := 3788391901894490007300315545600, coefficient := (-3788391901894490007300315545600) }, { argument := 3788150082879562223510074949632, coefficient := (-3788150082879562223510074949632) }, { argument := 101529697204426779880419491840, coefficient := (-101529697204426779880419491840) }, { argument := 197117249368781656906792960, coefficient := (-197117249368781656906792960) }, { argument := 16156003091050982383990865920, coefficient := (-16156003091050982383990865920) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 164928562852875793206261841920, coefficient := (-164928562852875793206261841920) }, { argument := 983763385711404490917150720, coefficient := (-983763385711404490917150720) }, { argument := 71732746874789910796042240, coefficient := (-71732746874789910796042240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 983763385711404490917150720, coefficient := (-983763385711404490917150720) }, { argument := 23015964211539734235415838720, coefficient := (-23015964211539734235415838720) }, { argument := 1844556348208883420469657600, coefficient := (-1844556348208883420469657600) }, { argument := 16156014758616609005282263040, coefficient := (-16156014758616609005282263040) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 71732746874789910796042240, coefficient := (-71732746874789910796042240) }, { argument := 1844556348208883420469657600, coefficient := (-1844556348208883420469657600) }, { argument := 71732746874789910796042240, coefficient := (-71732746874789910796042240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 207364784636608787020513280, coefficient := (-207364784636608787020513280) }, { argument := 17507655289497018022829752320, coefficient := (-17507655289497018022829752320) }, { argument := 638590894125197610640308436992, coefficient := (-638590894125197610640308436992) }, { argument := 638590993855213602141785554944, coefficient := (-638590993855213602141785554944) }] }

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

end TermShard6


end Parent3

namespace Parent3

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-59074621797865213260081087381504)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    7592691909, 3963918015, 6966438209, 3963918015, 15435, 3969,
    15435, 13671, 639891, 174195, 3969, 639891,
    15435, 15435, 6615, 15435, 174195, 6615,
    15435, 13671, 99225, 25515, 99225, 87885,
    4113585, 1119825, 25515, 4113585, 99225, 99225,
    42525, 99225, 1119825, 42525, 99225, 87885,
    167808701, 13681436919, 98735, 139477740045, 3255, 7595,
    98735, 98735, 3255, 1218455, 48825, 6840723393,
    98735, 7595, 48825, 7595, 98735, 98735,
    176697021, 15435, 3969, 15435, 13671, 639891,
    174195, 3969, 639891, 15435
  ]
def negativeCoefficients : Array ℕ := #[
    17507555559481026521352634368, 73121381151871779528234762240, 257016205493469065491920191488, 73121381151871779528234762240, 72889726663092973873397760, 74972290282038487412637696,
    72889726663092973873397760, 64559472187310919716438016, 3021799811089940145437147136, 822612629483477847999774720, 74972290282038487412637696, 3021799811089940145437147136,
    72889726663092973873397760, 72889726663092973873397760, 62476908568365406177198080, 72889726663092973873397760, 822612629483477847999774720, 62476908568365406177198080,
    72889726663092973873397760, 64559472187310919716438016, 1874307257050962185315942400, 1927858892966703962039255040, 1874307257050962185315942400, 1660100713387995078422691840,
    77703423713741318025526640640, 21152896186718001805708492800, 1927858892966703962039255040, 77703423713741318025526640640, 1874307257050962185315942400, 1874307257050962185315942400,
    1606549077472253301699379200, 1874307257050962185315942400, 21152896186718001805708492800, 1606549077472253301699379200, 1874307257050962185315942400, 1660100713387995078422691840,
    193470260043040506748338176, 15773622837837144797629906944, 1865051418744537680697098240, 160806885911844072445622353920, 983763385711404490917150720, 71732746874789910796042240,
    1865051418744537680697098240, 1865051418744537680697098240, 983763385711404490917150720, 23015964211539734235415838720, 1844556348208883420469657600, 15773634213713630753389019136,
    1865051418744537680697098240, 71732746874789910796042240, 1844556348208883420469657600, 71732746874789910796042240, 1865051418744537680697098240, 1865051418744537680697098240,
    203717795310867636862058496, 72889726663092973873397760, 74972290282038487412637696, 72889726663092973873397760, 64559472187310919716438016, 3021799811089940145437147136,
    822612629483477847999774720, 74972290282038487412637696, 3021799811089940145437147136, 72889726663092973873397760
  ]
def negativeScales : Array ℕ := #[
    32, 31, 32, 31, 13, 11,
    13, 13, 19, 17, 11, 19,
    13, 13, 12, 13, 17, 12,
    13, 13, 16, 14, 16, 16,
    21, 20, 14, 21, 16, 16,
    15, 16, 20, 15, 16, 16,
    27, 33, 16, 37, 11, 12,
    16, 16, 11, 20, 15, 32,
    16, 12, 15, 12, 16, 16,
    27, 13, 11, 13, 13, 19,
    17, 11, 19, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32821964323666687, 31884279981104318, 32697774079501420, 31884279981104318, 13913917868096136, 11954559858255908,
    13913917868096136, 13738831156120225, 19287466649624266, 17410343688621996, 11954559858255908, 19287466649624266,
    13913917868096136, 13913917868096136, 12691525441225267, 13913917868096136, 17410343688621996, 12691525441225267,
    13913917868096136, 13738831156120225, 16598416036779970, 14639058021287992, 16598416036779970, 16423329330216484,
    21971964838930244, 20094841862894057, 14639058021287992, 21971964838930244, 16598416036779970, 16598416036779970,
    15376023615438113, 16598416036779970, 20094841862894057, 15376023615438113, 16598416036779970, 16423329330216484,
    27322242281575724, 33671500708888984, 16591273967534972, 37021243937219061, 11668441828086828, 12890834253091783,
    16591273967534972, 16591273967534972, 11668441828086828, 20216621539732443, 15575332423664331, 32671501749354757,
    16591273967534972, 12890834253091783, 15575332423664331, 12890834253091783, 16591273967534972, 16591273967534972,
    27396702476267690, 13913917868096136, 11954559858255908, 13913917868096136, 13738831156120225, 19287466649624266,
    17410343688621996, 11954559858255908, 19287466649624266, 13913917868096136
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
noncomputable def negativeCeiling : ℝ := 158232723 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 17507555559481026521352634368, coefficient := (-17507555559481026521352634368) }, { argument := 73121381151871779528234762240, coefficient := (-73121381151871779528234762240) }, { argument := 257016205493469065491920191488, coefficient := (-257016205493469065491920191488) }, { argument := 73121381151871779528234762240, coefficient := (-73121381151871779528234762240) }, { argument := 72889726663092973873397760, coefficient := (-72889726663092973873397760) }, { argument := 74972290282038487412637696, coefficient := (-74972290282038487412637696) }, { argument := 72889726663092973873397760, coefficient := (-72889726663092973873397760) }, { argument := 64559472187310919716438016, coefficient := (-64559472187310919716438016) }, { argument := 3021799811089940145437147136, coefficient := (-3021799811089940145437147136) }, { argument := 822612629483477847999774720, coefficient := (-822612629483477847999774720) }, { argument := 74972290282038487412637696, coefficient := (-74972290282038487412637696) }, { argument := 3021799811089940145437147136, coefficient := (-3021799811089940145437147136) }, { argument := 72889726663092973873397760, coefficient := (-72889726663092973873397760) }, { argument := 72889726663092973873397760, coefficient := (-72889726663092973873397760) }, { argument := 62476908568365406177198080, coefficient := (-62476908568365406177198080) }, { argument := 72889726663092973873397760, coefficient := (-72889726663092973873397760) }, { argument := 822612629483477847999774720, coefficient := (-822612629483477847999774720) }, { argument := 62476908568365406177198080, coefficient := (-62476908568365406177198080) }, { argument := 72889726663092973873397760, coefficient := (-72889726663092973873397760) }, { argument := 64559472187310919716438016, coefficient := (-64559472187310919716438016) }, { argument := 1874307257050962185315942400, coefficient := (-1874307257050962185315942400) }, { argument := 1927858892966703962039255040, coefficient := (-1927858892966703962039255040) }, { argument := 1874307257050962185315942400, coefficient := (-1874307257050962185315942400) }, { argument := 1660100713387995078422691840, coefficient := (-1660100713387995078422691840) }, { argument := 77703423713741318025526640640, coefficient := (-77703423713741318025526640640) }, { argument := 21152896186718001805708492800, coefficient := (-21152896186718001805708492800) }, { argument := 1927858892966703962039255040, coefficient := (-1927858892966703962039255040) }, { argument := 77703423713741318025526640640, coefficient := (-77703423713741318025526640640) }, { argument := 1874307257050962185315942400, coefficient := (-1874307257050962185315942400) }, { argument := 1874307257050962185315942400, coefficient := (-1874307257050962185315942400) }, { argument := 1606549077472253301699379200, coefficient := (-1606549077472253301699379200) }, { argument := 1874307257050962185315942400, coefficient := (-1874307257050962185315942400) }, { argument := 21152896186718001805708492800, coefficient := (-21152896186718001805708492800) }, { argument := 1606549077472253301699379200, coefficient := (-1606549077472253301699379200) }, { argument := 1874307257050962185315942400, coefficient := (-1874307257050962185315942400) }, { argument := 1660100713387995078422691840, coefficient := (-1660100713387995078422691840) }, { argument := 193470260043040506748338176, coefficient := (-193470260043040506748338176) }, { argument := 15773622837837144797629906944, coefficient := (-15773622837837144797629906944) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 160806885911844072445622353920, coefficient := (-160806885911844072445622353920) }, { argument := 983763385711404490917150720, coefficient := (-983763385711404490917150720) }, { argument := 71732746874789910796042240, coefficient := (-71732746874789910796042240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 983763385711404490917150720, coefficient := (-983763385711404490917150720) }, { argument := 23015964211539734235415838720, coefficient := (-23015964211539734235415838720) }, { argument := 1844556348208883420469657600, coefficient := (-1844556348208883420469657600) }, { argument := 15773634213713630753389019136, coefficient := (-15773634213713630753389019136) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 71732746874789910796042240, coefficient := (-71732746874789910796042240) }, { argument := 1844556348208883420469657600, coefficient := (-1844556348208883420469657600) }, { argument := 71732746874789910796042240, coefficient := (-71732746874789910796042240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 1865051418744537680697098240, coefficient := (-1865051418744537680697098240) }, { argument := 203717795310867636862058496, coefficient := (-203717795310867636862058496) }, { argument := 72889726663092973873397760, coefficient := (-72889726663092973873397760) }, { argument := 74972290282038487412637696, coefficient := (-74972290282038487412637696) }, { argument := 72889726663092973873397760, coefficient := (-72889726663092973873397760) }, { argument := 64559472187310919716438016, coefficient := (-64559472187310919716438016) }, { argument := 3021799811089940145437147136, coefficient := (-3021799811089940145437147136) }, { argument := 822612629483477847999774720, coefficient := (-822612629483477847999774720) }, { argument := 74972290282038487412637696, coefficient := (-74972290282038487412637696) }, { argument := 3021799811089940145437147136, coefficient := (-3021799811089940145437147136) }, { argument := 72889726663092973873397760, coefficient := (-72889726663092973873397760) }] }

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

end TermShard7


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk9
