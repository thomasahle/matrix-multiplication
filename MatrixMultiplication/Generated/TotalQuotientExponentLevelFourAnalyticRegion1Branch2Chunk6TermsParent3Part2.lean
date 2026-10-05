import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 6, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6

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
def constantNumerator : ℤ := (-148894252816730365357772718997504)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1755, 8145, 7857, 16818911, 2111619829, 2743641725,
    1055810333, 8409093, 2205, 7887, 8295, 4281,
    114021, 177255, 7887, 114021, 8295, 4095,
    7605, 4095, 177255, 7605, 2205, 4281,
    184365, 176259, 22305, 171759, 6090219, 46215,
    176259, 6090219, 22305, 177255, 158535, 177255,
    46215, 158535, 184365, 171759, 422168475, 55503090681,
    286027960377, 27751554021, 26384067, 8145, 3681, 7695,
    7857, 219717, 158535, 3681, 219717, 7695,
    7605, 1755, 7605, 158535, 1755, 8145,
    7857, 177533705, 22367548351, 464692534733
  ]
def negativeCoefficients : Array ℕ := #[
    265208101677959275201167360, 307709400023786082124431360, 296829067647254419552075776, 19390884175968649279963136, 2434531910408332923690287104, 25305628365513000672349388800,
    2434532875403632279621206016, 19390048307877809315905536, 333210179031282166278389760, 297962435603143134403362816, 313376239803229656380866560, 323463214610639218557321216,
    8615183179892477070573305856, 6696504567368471698829475840, 297962435603143134403362816, 8615183179892477070573305856, 313376239803229656380866560, 309409451957619154401361920,
    287308776817789214801264640, 309409451957619154401361920, 6696504567368471698829475840, 287308776817789214801264640, 333210179031282166278389760, 323463214610639218557321216,
    6965112772914097118584504320, 6658876751232966365766746112, 6741272601626075935455313920, 6488871557849659138073690112, 230081968631487102429683515392, 111741013506980174618091847680,
    6658876751232966365766746112, 230081968631487102429683515392, 6741272601626075935455313920, 6696504567368471698829475840, 5989282962893913631626362880, 6696504567368471698829475840,
    111741013506980174618091847680, 5989282962893913631626362880, 6965112772914097118584504320, 6488871557849659138073690112, 486727113394578062416281600, 63990706818268786962418630656,
    659535572874956899628460539904, 63990726834139028441888980992, 486700131572605748376502272, 307709400023786082124431360, 278128496375090624505839616, 290708880685455359355125760,
    296829067647254419552075776, 8300673572133358699341152256, 5989282962893913631626362880, 278128496375090624505839616, 8300673572133358699341152256, 290708880685455359355125760,
    287308776817789214801264640, 265208101677959275201167360, 287308776817789214801264640, 5989282962893913631626362880, 265208101677959275201167360, 307709400023786082124431360,
    296829067647254419552075776, 409364852574056224034652160, 51576054998402637962676273152, 535754016323939857904496017408
  ]
def negativeScales : Array ℕ := #[
    10, 12, 12, 24, 30, 31,
    29, 23, 11, 12, 13, 12,
    16, 17, 12, 16, 13, 11,
    12, 11, 17, 12, 11, 12,
    17, 17, 14, 17, 22, 15,
    17, 22, 14, 17, 17, 17,
    15, 17, 17, 17, 28, 35,
    38, 34, 24, 12, 11, 12,
    12, 17, 17, 11, 17, 12,
    12, 10, 12, 17, 10, 12,
    12, 27, 34, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    10777255315595305, 12991699004141302, 12939762853831857, 24003580960425196, 30975702988671341, 31353444955281073,
    29975703560524195, 23003518769927317, 11106562940444883, 12945260936959442, 13018026265843226, 12063732120196920,
    16798940034596984, 17435466797943745, 12945260936959442, 16798940034596984, 13018026265843226, 11999647760072134,
    12892732536443689, 11999647760072134, 17435466797943745, 12892732536443689, 11106562940444883, 12063732120196920,
    17492205273810185, 17427337399601406, 14445079527660976, 17390026171239616, 22538062676690401, 15496073562648108,
    17427337399601406, 22538062676690401, 14445079527660976, 17435466797943745, 17274441855824639, 17435466797943745,
    15496073562648108, 17274441855824639, 17492205273810185, 17390026171239616, 28653243610049537, 35691849058882585,
    38057365226868008, 34691849510147990, 24653163631723499, 12991699004141302, 11845882035984914, 12909705616407956,
    12939762853831857, 17745286973289567, 17274441855824639, 11845882035984914, 17745286973289567, 12909705616407956,
    12892732536443689, 10777255315595305, 12892732536443689, 17274441855824639, 10777255315595305, 12991699004141302,
    12939762853831857, 27403517707210331, 34380688083872048, 38757485512222231
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
noncomputable def negativeCeiling : ℝ := 835571907 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 265208101677959275201167360, coefficient := (-265208101677959275201167360) }, { argument := 307709400023786082124431360, coefficient := (-307709400023786082124431360) }, { argument := 296829067647254419552075776, coefficient := (-296829067647254419552075776) }, { argument := 19390884175968649279963136, coefficient := (-19390884175968649279963136) }, { argument := 2434531910408332923690287104, coefficient := (-2434531910408332923690287104) }, { argument := 25305628365513000672349388800, coefficient := (-25305628365513000672349388800) }, { argument := 2434532875403632279621206016, coefficient := (-2434532875403632279621206016) }, { argument := 19390048307877809315905536, coefficient := (-19390048307877809315905536) }, { argument := 333210179031282166278389760, coefficient := (-333210179031282166278389760) }, { argument := 297962435603143134403362816, coefficient := (-297962435603143134403362816) }, { argument := 313376239803229656380866560, coefficient := (-313376239803229656380866560) }, { argument := 323463214610639218557321216, coefficient := (-323463214610639218557321216) }, { argument := 8615183179892477070573305856, coefficient := (-8615183179892477070573305856) }, { argument := 6696504567368471698829475840, coefficient := (-6696504567368471698829475840) }, { argument := 297962435603143134403362816, coefficient := (-297962435603143134403362816) }, { argument := 8615183179892477070573305856, coefficient := (-8615183179892477070573305856) }, { argument := 313376239803229656380866560, coefficient := (-313376239803229656380866560) }, { argument := 309409451957619154401361920, coefficient := (-309409451957619154401361920) }, { argument := 287308776817789214801264640, coefficient := (-287308776817789214801264640) }, { argument := 309409451957619154401361920, coefficient := (-309409451957619154401361920) }, { argument := 6696504567368471698829475840, coefficient := (-6696504567368471698829475840) }, { argument := 287308776817789214801264640, coefficient := (-287308776817789214801264640) }, { argument := 333210179031282166278389760, coefficient := (-333210179031282166278389760) }, { argument := 323463214610639218557321216, coefficient := (-323463214610639218557321216) }, { argument := 6965112772914097118584504320, coefficient := (-6965112772914097118584504320) }, { argument := 6658876751232966365766746112, coefficient := (-6658876751232966365766746112) }, { argument := 6741272601626075935455313920, coefficient := (-6741272601626075935455313920) }, { argument := 6488871557849659138073690112, coefficient := (-6488871557849659138073690112) }, { argument := 230081968631487102429683515392, coefficient := (-230081968631487102429683515392) }, { argument := 111741013506980174618091847680, coefficient := (-111741013506980174618091847680) }, { argument := 6658876751232966365766746112, coefficient := (-6658876751232966365766746112) }, { argument := 230081968631487102429683515392, coefficient := (-230081968631487102429683515392) }, { argument := 6741272601626075935455313920, coefficient := (-6741272601626075935455313920) }, { argument := 6696504567368471698829475840, coefficient := (-6696504567368471698829475840) }, { argument := 5989282962893913631626362880, coefficient := (-5989282962893913631626362880) }, { argument := 6696504567368471698829475840, coefficient := (-6696504567368471698829475840) }, { argument := 111741013506980174618091847680, coefficient := (-111741013506980174618091847680) }, { argument := 5989282962893913631626362880, coefficient := (-5989282962893913631626362880) }, { argument := 6965112772914097118584504320, coefficient := (-6965112772914097118584504320) }, { argument := 6488871557849659138073690112, coefficient := (-6488871557849659138073690112) }, { argument := 486727113394578062416281600, coefficient := (-486727113394578062416281600) }, { argument := 63990706818268786962418630656, coefficient := (-63990706818268786962418630656) }, { argument := 659535572874956899628460539904, coefficient := (-659535572874956899628460539904) }, { argument := 63990726834139028441888980992, coefficient := (-63990726834139028441888980992) }, { argument := 486700131572605748376502272, coefficient := (-486700131572605748376502272) }, { argument := 307709400023786082124431360, coefficient := (-307709400023786082124431360) }, { argument := 278128496375090624505839616, coefficient := (-278128496375090624505839616) }, { argument := 290708880685455359355125760, coefficient := (-290708880685455359355125760) }, { argument := 296829067647254419552075776, coefficient := (-296829067647254419552075776) }, { argument := 8300673572133358699341152256, coefficient := (-8300673572133358699341152256) }, { argument := 5989282962893913631626362880, coefficient := (-5989282962893913631626362880) }, { argument := 278128496375090624505839616, coefficient := (-278128496375090624505839616) }, { argument := 8300673572133358699341152256, coefficient := (-8300673572133358699341152256) }, { argument := 290708880685455359355125760, coefficient := (-290708880685455359355125760) }, { argument := 287308776817789214801264640, coefficient := (-287308776817789214801264640) }, { argument := 265208101677959275201167360, coefficient := (-265208101677959275201167360) }, { argument := 287308776817789214801264640, coefficient := (-287308776817789214801264640) }, { argument := 5989282962893913631626362880, coefficient := (-5989282962893913631626362880) }, { argument := 265208101677959275201167360, coefficient := (-265208101677959275201167360) }, { argument := 307709400023786082124431360, coefficient := (-307709400023786082124431360) }, { argument := 296829067647254419552075776, coefficient := (-296829067647254419552075776) }, { argument := 409364852574056224034652160, coefficient := (-409364852574056224034652160) }, { argument := 51576054998402637962676273152, coefficient := (-51576054998402637962676273152) }, { argument := 535754016323939857904496017408, coefficient := (-535754016323939857904496017408) }] }

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
def constantNumerator : ℤ := (-142058607311399856868583584825344)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1397972317, 355051779, 359101695, 13261900545, 26522747991, 719256489,
    106848564627, 186706233, 577101167469, 12981591, 16599111, 415073331,
    175164261, 106974190995, 186706233, 16353747, 875875544385, 47174117216959,
    8925, 285, 15885, 184365, 23587059976809, 15885,
    8925, 2205, 8145, 2205, 184365, 8145,
    437936403863, 285, 421808265743, 30771163413845, 320642863587143, 30771164270933,
    421806721551, 285, 8331, 8655, 4371, 128103,
    171759, 8331, 128103, 8655, 4281, 7857,
    4281, 171759, 7857, 285, 4371, 188908629,
    23295566235, 485933011647, 5823894063, 377802729, 376608513, 13919676671,
    27838200745, 754369623, 16564755, 2071044537
  ]
def negativeCoefficients : Array ℕ := #[
    51576075107659521315301228544, 409346831258017714409570304, 6624257064100304922995589120, 244638885284604222747936030720, 244629172160735583020387401728, 6633970187968944650544218112,
    240601577919614779964522496, 430515262139673089792802816, 2599032602768466608205594624, 478936173693142503744602112, 19137472029256064314638336, 478546969298695819735597056,
    403901286690932892182249472, 240884463351671134365941760, 430515262139673089792802816, 18854586597199709913219072, 986148193828804082521866240, 53113334179957163051676860416,
    337176966876892668257894400, 344543858590169314791260160, 9601893322289192220103802880, 6965112772914097118584504320, 53113337261161276211705413632, 9601893322289192220103802880,
    337176966876892668257894400, 333210179031282166278389760, 307709400023786082124431360, 333210179031282166278389760, 6965112772914097118584504320, 307709400023786082124431360,
    986145112624690922493313024, 344543858590169314791260160, 237456943552746244135714816, 34645250021087245398997729280, 361011770242516498795810783232, 34645250986082544754928648192,
    237456074249931770573094912, 344543858590169314791260160, 314736281350296114202411008, 326976655273894234596311040, 330263422345971507665043456, 9679189016880802572961579008,
    6488871557849659138073690112, 314736281350296114202411008, 9679189016880802572961579008, 326976655273894234596311040, 323463214610639218557321216, 296829067647254419552075776,
    323463214610639218557321216, 6488871557849659138073690112, 296829067647254419552075776, 344543858590169314791260160, 330263422345971507665043456, 435593641559793292497911808,
    53715918548649322727834910720, 560242618926195735744554729472, 53715941646278746021407227904, 435576890763252859618197504, 6947200855291316627998507008, 256772713138722350059105550336,
    256762082307782787355073576960, 6957831686230879332030480384, 19097862258043791479930880, 2387751783705830762439770112
  ]
def negativeScales : Array ℕ := #[
    30, 28, 28, 33, 34, 29,
    36, 27, 39, 23, 23, 28,
    27, 36, 27, 23, 39, 45,
    13, 8, 13, 17, 44, 13,
    13, 11, 12, 11, 17, 12,
    38, 8, 38, 44, 48, 44,
    38, 8, 13, 13, 12, 16,
    17, 13, 16, 13, 12, 12,
    12, 17, 12, 8, 12, 27,
    34, 38, 32, 28, 28, 33,
    34, 29, 23, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30380688646371827, 28403454194587275, 28419817221798848, 33626568489823481, 34626511208031099, 29421931090851994,
    36636776571152272, 27476194850391514, 39070033293328486, 23629963872457173, 23984602659794415, 28628790999002468,
    27384133209051200, 36638471812227228, 27476194850391514, 23963117903685033, 39671934931598670, 45423060754040158,
    13123636453803825, 8154818109052105, 13955377481012500, 17492205273810185, 44423060837733601, 13955377481012500,
    13123636453803825, 11106562940444883, 12991699004141302, 11106562940444883, 17492205273810185, 12991699004141302,
    38671930423914257, 8154818109052105, 38617796410190524, 44806644225221554, 48187960626501600, 44806644265405820,
    38617791128638691, 8154818109052105, 13024273962540003, 13079318104254002, 12093747662785669, 16966944750328079,
    17390026171239616, 13024273962540003, 16966944750328079, 13079318104254002, 12063732120196920, 12939762853831857,
    12063732120196920, 17390026171239616, 12939762853831857, 8154818109052105, 12093747662785669, 27493113361996278,
    34439336346694927, 38821966489407602, 32439336967047872, 28493057881949131, 28488490370639308, 33696406649310505,
    34696346918023592, 29490696341753658, 23981613547301422, 30947711442497337
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
noncomputable def negativeCeiling : ℝ := 42733553 / 40000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 51576075107659521315301228544, coefficient := (-51576075107659521315301228544) }, { argument := 409346831258017714409570304, coefficient := (-409346831258017714409570304) }, { argument := 6624257064100304922995589120, coefficient := (-6624257064100304922995589120) }, { argument := 244638885284604222747936030720, coefficient := (-244638885284604222747936030720) }, { argument := 244629172160735583020387401728, coefficient := (-244629172160735583020387401728) }, { argument := 6633970187968944650544218112, coefficient := (-6633970187968944650544218112) }, { argument := 240601577919614779964522496, coefficient := (-240601577919614779964522496) }, { argument := 430515262139673089792802816, coefficient := (-430515262139673089792802816) }, { argument := 2599032602768466608205594624, coefficient := (-2599032602768466608205594624) }, { argument := 478936173693142503744602112, coefficient := (-478936173693142503744602112) }, { argument := 19137472029256064314638336, coefficient := (-19137472029256064314638336) }, { argument := 478546969298695819735597056, coefficient := (-478546969298695819735597056) }, { argument := 403901286690932892182249472, coefficient := (-403901286690932892182249472) }, { argument := 240884463351671134365941760, coefficient := (-240884463351671134365941760) }, { argument := 430515262139673089792802816, coefficient := (-430515262139673089792802816) }, { argument := 18854586597199709913219072, coefficient := (-18854586597199709913219072) }, { argument := 986148193828804082521866240, coefficient := (-986148193828804082521866240) }, { argument := 53113334179957163051676860416, coefficient := (-53113334179957163051676860416) }, { argument := 337176966876892668257894400, coefficient := (-337176966876892668257894400) }, { argument := 344543858590169314791260160, coefficient := (-344543858590169314791260160) }, { argument := 9601893322289192220103802880, coefficient := (-9601893322289192220103802880) }, { argument := 6965112772914097118584504320, coefficient := (-6965112772914097118584504320) }, { argument := 53113337261161276211705413632, coefficient := (-53113337261161276211705413632) }, { argument := 9601893322289192220103802880, coefficient := (-9601893322289192220103802880) }, { argument := 337176966876892668257894400, coefficient := (-337176966876892668257894400) }, { argument := 333210179031282166278389760, coefficient := (-333210179031282166278389760) }, { argument := 307709400023786082124431360, coefficient := (-307709400023786082124431360) }, { argument := 333210179031282166278389760, coefficient := (-333210179031282166278389760) }, { argument := 6965112772914097118584504320, coefficient := (-6965112772914097118584504320) }, { argument := 307709400023786082124431360, coefficient := (-307709400023786082124431360) }, { argument := 986145112624690922493313024, coefficient := (-986145112624690922493313024) }, { argument := 344543858590169314791260160, coefficient := (-344543858590169314791260160) }, { argument := 237456943552746244135714816, coefficient := (-237456943552746244135714816) }, { argument := 34645250021087245398997729280, coefficient := (-34645250021087245398997729280) }, { argument := 361011770242516498795810783232, coefficient := (-361011770242516498795810783232) }, { argument := 34645250986082544754928648192, coefficient := (-34645250986082544754928648192) }, { argument := 237456074249931770573094912, coefficient := (-237456074249931770573094912) }, { argument := 344543858590169314791260160, coefficient := (-344543858590169314791260160) }, { argument := 314736281350296114202411008, coefficient := (-314736281350296114202411008) }, { argument := 326976655273894234596311040, coefficient := (-326976655273894234596311040) }, { argument := 330263422345971507665043456, coefficient := (-330263422345971507665043456) }, { argument := 9679189016880802572961579008, coefficient := (-9679189016880802572961579008) }, { argument := 6488871557849659138073690112, coefficient := (-6488871557849659138073690112) }, { argument := 314736281350296114202411008, coefficient := (-314736281350296114202411008) }, { argument := 9679189016880802572961579008, coefficient := (-9679189016880802572961579008) }, { argument := 326976655273894234596311040, coefficient := (-326976655273894234596311040) }, { argument := 323463214610639218557321216, coefficient := (-323463214610639218557321216) }, { argument := 296829067647254419552075776, coefficient := (-296829067647254419552075776) }, { argument := 323463214610639218557321216, coefficient := (-323463214610639218557321216) }, { argument := 6488871557849659138073690112, coefficient := (-6488871557849659138073690112) }, { argument := 296829067647254419552075776, coefficient := (-296829067647254419552075776) }, { argument := 344543858590169314791260160, coefficient := (-344543858590169314791260160) }, { argument := 330263422345971507665043456, coefficient := (-330263422345971507665043456) }, { argument := 435593641559793292497911808, coefficient := (-435593641559793292497911808) }, { argument := 53715918548649322727834910720, coefficient := (-53715918548649322727834910720) }, { argument := 560242618926195735744554729472, coefficient := (-560242618926195735744554729472) }, { argument := 53715941646278746021407227904, coefficient := (-53715941646278746021407227904) }, { argument := 435576890763252859618197504, coefficient := (-435576890763252859618197504) }, { argument := 6947200855291316627998507008, coefficient := (-6947200855291316627998507008) }, { argument := 256772713138722350059105550336, coefficient := (-256772713138722350059105550336) }, { argument := 256762082307782787355073576960, coefficient := (-256762082307782787355073576960) }, { argument := 6957831686230879332030480384, coefficient := (-6957831686230879332030480384) }, { argument := 19097862258043791479930880, coefficient := (-19097862258043791479930880) }, { argument := 2387751783705830762439770112, coefficient := (-2387751783705830762439770112) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk6
