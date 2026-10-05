import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 2, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-189000072832788169891205330501632)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    35, 1451, 1451, 1451, 1451, 489417471,
    22120779321, 61503705, 9, 9, 9, 9,
    15994035, 722901285, 2009925, 6438699, 1277018325, 1277018325,
    6438699, 395, 395, 395, 395, 9596421,
    433740771, 1205955, 1451, 1451, 1451, 1451,
    7840275957, 354366209907, 985265235, 1380027819, 273707594325, 273707594325,
    1380027819, 502212699, 22699100349, 63111645, 2496068979, 495057437325,
    495057437325, 2496068979, 2765735, 113312675, 2333195725, 113312675,
    2765735, 295546641, 1179116049, 585975757, 1179116049, 1461519089,
    113312675, 34029168119, 747863655, 36975715, 373335445, 759791305,
    182875555, 113312675, 36975715, 18904878555
  ]
def negativeCoefficients : Array ℕ := #[
    169249614746048084458864640, 7016605457043307729994645504, 7016605457043307729994645504, 7016605457043307729994645504, 7016605457043307729994645504, 564259927046197896277917696,
    25503522177843346821712183296, 567271552859965259136368640, 174085318024506601157689344, 174085318024506601157689344, 174085318024506601157689344, 174085318024506601157689344,
    590075740701906296761221120, 26670349989901539159960453120, 593225153317610728508620800, 118773032620649616280387584, 23556830218712248141165363200, 23556830218712248141165363200,
    118773032620649616280387584, 1910102794991114096035758080, 1910102794991114096035758080, 1910102794991114096035758080, 1910102794991114096035758080, 354045444421143778056732672,
    16002209993940923495976271872, 355935091990566437105172480, 7016605457043307729994645504, 7016605457043307729994645504, 7016605457043307729994645504, 7016605457043307729994645504,
    9039222752877327083510956032, 408556423907804203006644191232, 9087467817384149347341434880, 1591063749480785484756025344, 315563371471499490724361011200, 315563371471499490724361011200,
    1591063749480785484756025344, 579011820563745553696948224, 26170280927590885300711194624, 582102181692905527349084160, 2877771602871156327793557504, 570762365507548845586985779200,
    570762365507548845586985779200, 2877771602871156327793557504, 204075222882804346954711040, 33443998656518823466552524800, 344318915303585685776944332800, 33443998656518823466552524800,
    204075222882804346954711040, 1362968312092878597431230464, 1359428249319160704688717824, 1351168102847152288289521664, 1359428249319160704688717824, 1685016787101508295525924864,
    33443998656518823466552524800, 39232959708276828744810758144, 27591298891628029359905832960, 1364163103094846746662010880, 27547293630237873013239316480, 28031351505529592826570997760,
    1686729280211297580288573440, 33443998656518823466552524800, 1364163103094846746662010880, 21795841028040315102748999680
  ]
def negativeScales : Array ℕ := #[
    5, 10, 10, 10, 10, 28,
    34, 25, 3, 3, 3, 3,
    23, 29, 20, 22, 30, 30,
    22, 8, 8, 8, 8, 23,
    28, 20, 10, 10, 10, 10,
    32, 38, 29, 30, 37, 37,
    30, 28, 34, 25, 31, 38,
    38, 31, 21, 26, 31, 26,
    21, 28, 30, 29, 30, 30,
    26, 34, 29, 25, 28, 29,
    27, 26, 25, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    5129283016944967, 10502831804067043, 10502831804067043, 10502831804067043, 10502831804067043, 28866490364465229,
    34364683161875569, 25874169988353088, 3169925001442313, 3169925001442313, 3169925001442313, 3169925001442313,
    23931030621834616, 29429223414070299, 20938710246423341, 22618337776949349, 30250132081608682, 30250132081608682,
    22618337776949349, 8625708843075807, 8625708843075807, 8625708843075807, 8625708843075807, 23194065020128625,
    28692257819964341, 20201744643653310, 10502831804067043, 10502831804067043, 10502831804067043, 10502831804067043,
    32868257290718741, 38366450088049757, 29875936914617886, 30362050203546823, 37993844529671255, 37993844529671255,
    30362050203546823, 28903723272967495, 34401916068074550, 25911402897174510, 31217010657692093, 38848804964053774,
    38848804964053774, 31217010657692093, 21399231500034915, 26755734007421834, 31119660189873691, 26755734007421834,
    21399231500034915, 28138810583002944, 30135058569825227, 29126265737774810, 30135058569825227, 30444821526391153,
    26755734007421834, 34986052851239296, 29478200031638281, 25140074709222989, 28475897245768850, 29501027961092694,
    27446287001833352, 26755734007421834, 25140074709222989, 34138039530351006
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
noncomputable def negativeCeiling : ℝ := 1314813827 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 564259927046197896277917696, coefficient := (-564259927046197896277917696) }, { argument := 25503522177843346821712183296, coefficient := (-25503522177843346821712183296) }, { argument := 567271552859965259136368640, coefficient := (-567271552859965259136368640) }, { argument := 174085318024506601157689344, coefficient := (-174085318024506601157689344) }, { argument := 174085318024506601157689344, coefficient := (-174085318024506601157689344) }, { argument := 174085318024506601157689344, coefficient := (-174085318024506601157689344) }, { argument := 174085318024506601157689344, coefficient := (-174085318024506601157689344) }, { argument := 590075740701906296761221120, coefficient := (-590075740701906296761221120) }, { argument := 26670349989901539159960453120, coefficient := (-26670349989901539159960453120) }, { argument := 593225153317610728508620800, coefficient := (-593225153317610728508620800) }, { argument := 118773032620649616280387584, coefficient := (-118773032620649616280387584) }, { argument := 23556830218712248141165363200, coefficient := (-23556830218712248141165363200) }, { argument := 23556830218712248141165363200, coefficient := (-23556830218712248141165363200) }, { argument := 118773032620649616280387584, coefficient := (-118773032620649616280387584) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 354045444421143778056732672, coefficient := (-354045444421143778056732672) }, { argument := 16002209993940923495976271872, coefficient := (-16002209993940923495976271872) }, { argument := 355935091990566437105172480, coefficient := (-355935091990566437105172480) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 9039222752877327083510956032, coefficient := (-9039222752877327083510956032) }, { argument := 408556423907804203006644191232, coefficient := (-408556423907804203006644191232) }, { argument := 9087467817384149347341434880, coefficient := (-9087467817384149347341434880) }, { argument := 1591063749480785484756025344, coefficient := (-1591063749480785484756025344) }, { argument := 315563371471499490724361011200, coefficient := (-315563371471499490724361011200) }, { argument := 315563371471499490724361011200, coefficient := (-315563371471499490724361011200) }, { argument := 1591063749480785484756025344, coefficient := (-1591063749480785484756025344) }, { argument := 579011820563745553696948224, coefficient := (-579011820563745553696948224) }, { argument := 26170280927590885300711194624, coefficient := (-26170280927590885300711194624) }, { argument := 582102181692905527349084160, coefficient := (-582102181692905527349084160) }, { argument := 2877771602871156327793557504, coefficient := (-2877771602871156327793557504) }, { argument := 570762365507548845586985779200, coefficient := (-570762365507548845586985779200) }, { argument := 570762365507548845586985779200, coefficient := (-570762365507548845586985779200) }, { argument := 2877771602871156327793557504, coefficient := (-2877771602871156327793557504) }, { argument := 204075222882804346954711040, coefficient := (-204075222882804346954711040) }, { argument := 33443998656518823466552524800, coefficient := (-33443998656518823466552524800) }, { argument := 344318915303585685776944332800, coefficient := (-344318915303585685776944332800) }, { argument := 33443998656518823466552524800, coefficient := (-33443998656518823466552524800) }, { argument := 204075222882804346954711040, coefficient := (-204075222882804346954711040) }, { argument := 1362968312092878597431230464, coefficient := (-1362968312092878597431230464) }, { argument := 1359428249319160704688717824, coefficient := (-1359428249319160704688717824) }, { argument := 1351168102847152288289521664, coefficient := (-1351168102847152288289521664) }, { argument := 1359428249319160704688717824, coefficient := (-1359428249319160704688717824) }, { argument := 1685016787101508295525924864, coefficient := (-1685016787101508295525924864) }, { argument := 33443998656518823466552524800, coefficient := (-33443998656518823466552524800) }, { argument := 39232959708276828744810758144, coefficient := (-39232959708276828744810758144) }, { argument := 27591298891628029359905832960, coefficient := (-27591298891628029359905832960) }, { argument := 1364163103094846746662010880, coefficient := (-1364163103094846746662010880) }, { argument := 27547293630237873013239316480, coefficient := (-27547293630237873013239316480) }, { argument := 28031351505529592826570997760, coefficient := (-28031351505529592826570997760) }, { argument := 1686729280211297580288573440, coefficient := (-1686729280211297580288573440) }, { argument := 33443998656518823466552524800, coefficient := (-33443998656518823466552524800) }, { argument := 1364163103094846746662010880, coefficient := (-1364163103094846746662010880) }, { argument := 21795841028040315102748999680, coefficient := (-21795841028040315102748999680) }] }

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


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-253068150401507211584891846131712)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    28920709125, 926464275, 75118725, 16100446725, 29121025725, 28920709125,
    16100446725, 475751925, 475751925, 926464275, 926464275, 29121025725,
    926464275, 18904878555, 75118725, 489417471, 22120779321, 61503705,
    1380027819, 273707594325, 273707594325, 1380027819, 499186795, 34029168119,
    11132679789, 221566016645, 433740771, 722901285, 22120779321, 722901285,
    433740771, 354366209907, 22699100349, 34029168119, 22120779321, 722901285,
    22699100349, 722901285, 22120779321, 722901285, 499186795, 40778427,
    8087782725, 8087782725, 40778427, 18253851, 747863655, 15399091785,
    747863655, 18253851, 295546641, 35, 2636944765, 395,
    35, 5273888245, 35, 35, 1451, 9,
    395, 1451, 295546641, 35
  ]
def negativeCoefficients : Array ℕ := #[
    33343307478691968876281856000, 17090249374359866298492518400, 22171134323493880603449753600, 297000820208470108917045657600, 537188108712987148787751321600, 33343307478691968876281856000,
    297000820208470108917045657600, 17552148006099322144397721600, 17552148006099322144397721600, 17090249374359866298492518400, 17090249374359866298492518400, 537188108712987148787751321600,
    17090249374359866298492518400, 21795841028040315102748999680, 22171134323493880603449753600, 564259927046197896277917696, 25503522177843346821712183296, 567271552859965259136368640,
    1591063749480785484756025344, 315563371471499490724361011200, 315563371471499490724361011200, 1591063749480785484756025344, 1151046381542539354009763840, 39232959708276828744810758144,
    25670211865280231441461936128, 255448225280099101265383915520, 16002209993940923495976271872, 833448437184423098748764160, 25503522177843346821712183296, 26670349989901539159960453120,
    16002209993940923495976271872, 408556423907804203006644191232, 26170280927590885300711194624, 39232959708276828744810758144, 25503522177843346821712183296, 833448437184423098748764160,
    26170280927590885300711194624, 833448437184423098748764160, 25503522177843346821712183296, 26670349989901539159960453120, 1151046381542539354009763840, 94028650824680946221973504,
    18649157256480529778422579200, 18649157256480529778422579200, 94028650824680946221973504, 168362058878313586237636608, 27591298891628029359905832960, 284063105125458190765979074560,
    27591298891628029359905832960, 168362058878313586237636608, 1362968312092878597431230464, 169249614746048084458864640, 48643045216463176264308490240, 1910102794991114096035758080,
    169249614746048084458864640, 48643033364430108905921576960, 169249614746048084458864640, 169249614746048084458864640, 7016605457043307729994645504, 174085318024506601157689344,
    1910102794991114096035758080, 7016605457043307729994645504, 1362968312092878597431230464, 169249614746048084458864640
  ]
def negativeScales : Array ℕ := #[
    34, 29, 26, 33, 34, 34,
    33, 28, 28, 29, 29, 34,
    29, 34, 26, 28, 34, 25,
    30, 37, 37, 30, 28, 34,
    33, 37, 28, 29, 34, 29,
    28, 38, 34, 34, 34, 29,
    34, 29, 34, 29, 28, 25,
    32, 32, 25, 24, 29, 33,
    29, 24, 28, 5, 31, 8,
    5, 32, 5, 5, 10, 3,
    8, 10, 28, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34751383876172385, 29787160105762238, 26162669240358342, 33906381671859979, 34761342121397971, 34751383876172385,
    33906381671859979, 28825634254160643, 28825634254160643, 29787160105762238, 29787160105762238, 34761342121397971,
    29787160105762238, 34138039530351006, 26162669240358342, 28866490364465229, 34364683161875569, 25874169988353088,
    30362050203546823, 37993844529671255, 37993844529671255, 30362050203546823, 28895004534150419, 34986052851239296,
    33374081859877819, 37688945664475355, 28692257819964341, 29429223414070299, 34364683161875569, 29429223414070299,
    28692257819964341, 38366450088049757, 34401916068074550, 34986052851239296, 34364683161875569, 29429223414070299,
    34401916068074550, 29429223414070299, 34364683161875569, 29429223414070299, 28895004534150419, 25281302789662460,
    32913097099844375, 32913097099844375, 25281302789662460, 24121697524506000, 29478200031638281, 33842126215834057,
    29478200031638281, 24121697524506000, 28138810583002944, 5129283016944967, 31296220205964175, 8625708843075807,
    5129283016944967, 32296219854446885, 5129283016944967, 5129283016944967, 10502831804067043, 3169925001442313,
    8625708843075807, 10502831804067043, 28138810583002944, 5129283016944967
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
noncomputable def negativeCeiling : ℝ := 1703702719 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 33343307478691968876281856000, coefficient := (-33343307478691968876281856000) }, { argument := 17090249374359866298492518400, coefficient := (-17090249374359866298492518400) }, { argument := 22171134323493880603449753600, coefficient := (-22171134323493880603449753600) }, { argument := 297000820208470108917045657600, coefficient := (-297000820208470108917045657600) }, { argument := 537188108712987148787751321600, coefficient := (-537188108712987148787751321600) }, { argument := 33343307478691968876281856000, coefficient := (-33343307478691968876281856000) }, { argument := 297000820208470108917045657600, coefficient := (-297000820208470108917045657600) }, { argument := 17552148006099322144397721600, coefficient := (-17552148006099322144397721600) }, { argument := 17552148006099322144397721600, coefficient := (-17552148006099322144397721600) }, { argument := 17090249374359866298492518400, coefficient := (-17090249374359866298492518400) }, { argument := 17090249374359866298492518400, coefficient := (-17090249374359866298492518400) }, { argument := 537188108712987148787751321600, coefficient := (-537188108712987148787751321600) }, { argument := 17090249374359866298492518400, coefficient := (-17090249374359866298492518400) }, { argument := 21795841028040315102748999680, coefficient := (-21795841028040315102748999680) }, { argument := 22171134323493880603449753600, coefficient := (-22171134323493880603449753600) }, { argument := 564259927046197896277917696, coefficient := (-564259927046197896277917696) }, { argument := 25503522177843346821712183296, coefficient := (-25503522177843346821712183296) }, { argument := 567271552859965259136368640, coefficient := (-567271552859965259136368640) }, { argument := 1591063749480785484756025344, coefficient := (-1591063749480785484756025344) }, { argument := 315563371471499490724361011200, coefficient := (-315563371471499490724361011200) }, { argument := 315563371471499490724361011200, coefficient := (-315563371471499490724361011200) }, { argument := 1591063749480785484756025344, coefficient := (-1591063749480785484756025344) }, { argument := 1151046381542539354009763840, coefficient := (-1151046381542539354009763840) }, { argument := 39232959708276828744810758144, coefficient := (-39232959708276828744810758144) }, { argument := 25670211865280231441461936128, coefficient := (-25670211865280231441461936128) }, { argument := 255448225280099101265383915520, coefficient := (-255448225280099101265383915520) }, { argument := 16002209993940923495976271872, coefficient := (-16002209993940923495976271872) }, { argument := 833448437184423098748764160, coefficient := (-833448437184423098748764160) }, { argument := 25503522177843346821712183296, coefficient := (-25503522177843346821712183296) }, { argument := 26670349989901539159960453120, coefficient := (-26670349989901539159960453120) }, { argument := 16002209993940923495976271872, coefficient := (-16002209993940923495976271872) }, { argument := 408556423907804203006644191232, coefficient := (-408556423907804203006644191232) }, { argument := 26170280927590885300711194624, coefficient := (-26170280927590885300711194624) }, { argument := 39232959708276828744810758144, coefficient := (-39232959708276828744810758144) }, { argument := 25503522177843346821712183296, coefficient := (-25503522177843346821712183296) }, { argument := 833448437184423098748764160, coefficient := (-833448437184423098748764160) }, { argument := 26170280927590885300711194624, coefficient := (-26170280927590885300711194624) }, { argument := 833448437184423098748764160, coefficient := (-833448437184423098748764160) }, { argument := 25503522177843346821712183296, coefficient := (-25503522177843346821712183296) }, { argument := 26670349989901539159960453120, coefficient := (-26670349989901539159960453120) }, { argument := 1151046381542539354009763840, coefficient := (-1151046381542539354009763840) }, { argument := 94028650824680946221973504, coefficient := (-94028650824680946221973504) }, { argument := 18649157256480529778422579200, coefficient := (-18649157256480529778422579200) }, { argument := 18649157256480529778422579200, coefficient := (-18649157256480529778422579200) }, { argument := 94028650824680946221973504, coefficient := (-94028650824680946221973504) }, { argument := 168362058878313586237636608, coefficient := (-168362058878313586237636608) }, { argument := 27591298891628029359905832960, coefficient := (-27591298891628029359905832960) }, { argument := 284063105125458190765979074560, coefficient := (-284063105125458190765979074560) }, { argument := 27591298891628029359905832960, coefficient := (-27591298891628029359905832960) }, { argument := 168362058878313586237636608, coefficient := (-168362058878313586237636608) }, { argument := 1362968312092878597431230464, coefficient := (-1362968312092878597431230464) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 48643045216463176264308490240, coefficient := (-48643045216463176264308490240) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 48643033364430108905921576960, coefficient := (-48643033364430108905921576960) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 174085318024506601157689344, coefficient := (-174085318024506601157689344) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 1362968312092878597431230464, coefficient := (-1362968312092878597431230464) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2
