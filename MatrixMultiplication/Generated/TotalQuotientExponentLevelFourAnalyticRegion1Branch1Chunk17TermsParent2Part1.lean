import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 17, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17

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
def constantNumerator : ℤ := (-21559041667808792860706996911865856)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    301782845, 289067892442354701, 1005, 289067880765500403, 1005, 14396788995,
    4338334205, 2345, 4338337283, 2345, 331, 317,
    2077, 2345, 1005, 26465, 2345, 1005,
    2345, 2345, 97217, 603, 26465, 97217,
    2077, 2345, 603, 2345, 4063659369, 29605876993,
    8127324205, 8450176075, 2345, 8450182069, 2345, 4063659369,
    29605876993, 8127324205, 159768306389, 97217, 159768419627, 97217,
    8369, 8452174923, 603, 8452180917, 603, 2081,
    2908560291, 21190378027, 5817124495, 97954756675, 26465, 97954826173,
    26465, 331, 159768306389, 97217, 159768419627, 97217,
    128447, 8217, 3712022222222107, 2077
  ]
def negativeCoefficients : Array ℕ := #[
    695863863443869773793853440, 162730756586020406037952396787712, 151871306089087790072463360, 162730750012535822871405564788736, 151871306089087790072463360, 67986913810934564232092996075520,
    20007035196463797252726456320, 177183190437269088417873920, 20007049391233361972226424832, 177183190437269088417873920, 102439538250865217747902529536, 6131671757085399174109724672,
    156933682958724049741545472, 177183190437269088417873920, 151871306089087790072463360, 1999638863506322569287434240, 177183190437269088417873920, 151871306089087790072463360,
    177183190437269088417873920, 177183190437269088417873920, 7345508837842212779838144512, 182245567306905348086956032, 1999638863506322569287434240, 7345508837842212779838144512,
    156933682958724049741545472, 177183190437269088417873920, 182245567306905348086956032, 177183190437269088417873920, 18740321095668761502286872576, 68266504495949588794060046336,
    18740333701712492873551708160, 19484779429163561195562598400, 177183190437269088417873920, 19484793250386558422444146688, 177183190437269088417873920, 18740321095668761502286872576,
    68266504495949588794060046336, 18740333701712492873551708160, 736801264761974410595224518656, 7345508837842212779838144512, 736801786980075765275775991808, 7345508837842212779838144512,
    161880002949677305009855791104, 19489388458850841969291165696, 182245567306905348086956032, 19489402280073839196172713984, 182245567306905348086956032, 161009576359554772004067344384,
    13413366827757794724428120064, 48861685036153418867963592704, 13413375850521489777612554240, 225868290898277174146079129600, 1999638863506322569287434240, 225868451149754628479381405696,
    1999638863506322569287434240, 102439538250865217747902529536, 736801264761974410595224518656, 7345508837842212779838144512, 736801786980075765275775991808, 7345508837842212779838144512,
    2484526316032644377655747018752, 158939895356374526856970371072, 4179365474197620395399622688768, 156933682958724049741545472
  ]
def negativeScales : Array ℕ := #[
    28, 58, 9, 58, 9, 33,
    32, 11, 32, 11, 8, 8,
    11, 11, 9, 14, 11, 9,
    11, 11, 16, 9, 14, 16,
    11, 11, 9, 11, 31, 34,
    32, 32, 11, 32, 11, 31,
    34, 32, 37, 16, 37, 16,
    13, 32, 9, 32, 9, 11,
    31, 34, 32, 36, 14, 36,
    14, 8, 37, 16, 37, 16,
    16, 13, 51, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    28168935556557729, 58004185986733684, 9972979801353332, 58004185928456232, 9972979801353332, 33745028023412369,
    32014494049763656, 11195372207402739, 32014495073339423, 11195372207402739, 8370687406807220, 8308339030139408,
    11020285500844648, 11195372207402739, 9972979801353332, 14691798033581851, 11195372207402739, 9972979801353332,
    11195372207402739, 11195372207402739, 16568920994526853, 9236014191900085, 14691798033581851, 16568920994526853,
    11020285500844648, 11195372207402739, 9236014191900085, 11195372207402739, 31920132335354063, 34785164539631388,
    32920133305810895, 32976334273057804, 11195372207402739, 32976335296410834, 11195372207402739, 31920132335354063,
    34785164539631388, 32920133305810895, 37217190289634340, 16568920994526853, 37217191312164070, 16568920994526853,
    13030839532141380, 32976675495278989, 9236014191900085, 32976676518390009, 9236014191900085, 11023061249735335,
    31437658063816650, 34302690273856644, 32437659034273377, 36511396500221515, 14691798033581851, 36511397523800030,
    14691798033581851, 8370687406807220, 37217190289634340, 16568920994526853, 37217191312164070, 16568920994526853,
    16970813684326523, 13004396051426535, 51721126770691845, 11020285500844648
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
noncomputable def negativeCeiling : ℝ := 259748275379 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 695863863443869773793853440, coefficient := (-695863863443869773793853440) }, { argument := 162730756586020406037952396787712, coefficient := (-162730756586020406037952396787712) }, { argument := 151871306089087790072463360, coefficient := (-151871306089087790072463360) }, { argument := 162730750012535822871405564788736, coefficient := (-162730750012535822871405564788736) }, { argument := 151871306089087790072463360, coefficient := (-151871306089087790072463360) }, { argument := 67986913810934564232092996075520, coefficient := (-67986913810934564232092996075520) }, { argument := 20007035196463797252726456320, coefficient := (-20007035196463797252726456320) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 20007049391233361972226424832, coefficient := (-20007049391233361972226424832) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 102439538250865217747902529536, coefficient := (-102439538250865217747902529536) }, { argument := 6131671757085399174109724672, coefficient := (-6131671757085399174109724672) }, { argument := 156933682958724049741545472, coefficient := (-156933682958724049741545472) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 151871306089087790072463360, coefficient := (-151871306089087790072463360) }, { argument := 1999638863506322569287434240, coefficient := (-1999638863506322569287434240) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 151871306089087790072463360, coefficient := (-151871306089087790072463360) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 7345508837842212779838144512, coefficient := (-7345508837842212779838144512) }, { argument := 182245567306905348086956032, coefficient := (-182245567306905348086956032) }, { argument := 1999638863506322569287434240, coefficient := (-1999638863506322569287434240) }, { argument := 7345508837842212779838144512, coefficient := (-7345508837842212779838144512) }, { argument := 156933682958724049741545472, coefficient := (-156933682958724049741545472) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 182245567306905348086956032, coefficient := (-182245567306905348086956032) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 18740321095668761502286872576, coefficient := (-18740321095668761502286872576) }, { argument := 68266504495949588794060046336, coefficient := (-68266504495949588794060046336) }, { argument := 18740333701712492873551708160, coefficient := (-18740333701712492873551708160) }, { argument := 19484779429163561195562598400, coefficient := (-19484779429163561195562598400) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 19484793250386558422444146688, coefficient := (-19484793250386558422444146688) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 18740321095668761502286872576, coefficient := (-18740321095668761502286872576) }, { argument := 68266504495949588794060046336, coefficient := (-68266504495949588794060046336) }, { argument := 18740333701712492873551708160, coefficient := (-18740333701712492873551708160) }, { argument := 736801264761974410595224518656, coefficient := (-736801264761974410595224518656) }, { argument := 7345508837842212779838144512, coefficient := (-7345508837842212779838144512) }, { argument := 736801786980075765275775991808, coefficient := (-736801786980075765275775991808) }, { argument := 7345508837842212779838144512, coefficient := (-7345508837842212779838144512) }, { argument := 161880002949677305009855791104, coefficient := (-161880002949677305009855791104) }, { argument := 19489388458850841969291165696, coefficient := (-19489388458850841969291165696) }, { argument := 182245567306905348086956032, coefficient := (-182245567306905348086956032) }, { argument := 19489402280073839196172713984, coefficient := (-19489402280073839196172713984) }, { argument := 182245567306905348086956032, coefficient := (-182245567306905348086956032) }, { argument := 161009576359554772004067344384, coefficient := (-161009576359554772004067344384) }, { argument := 13413366827757794724428120064, coefficient := (-13413366827757794724428120064) }, { argument := 48861685036153418867963592704, coefficient := (-48861685036153418867963592704) }, { argument := 13413375850521489777612554240, coefficient := (-13413375850521489777612554240) }, { argument := 225868290898277174146079129600, coefficient := (-225868290898277174146079129600) }, { argument := 1999638863506322569287434240, coefficient := (-1999638863506322569287434240) }, { argument := 225868451149754628479381405696, coefficient := (-225868451149754628479381405696) }, { argument := 1999638863506322569287434240, coefficient := (-1999638863506322569287434240) }, { argument := 102439538250865217747902529536, coefficient := (-102439538250865217747902529536) }, { argument := 736801264761974410595224518656, coefficient := (-736801264761974410595224518656) }, { argument := 7345508837842212779838144512, coefficient := (-7345508837842212779838144512) }, { argument := 736801786980075765275775991808, coefficient := (-736801786980075765275775991808) }, { argument := 7345508837842212779838144512, coefficient := (-7345508837842212779838144512) }, { argument := 2484526316032644377655747018752, coefficient := (-2484526316032644377655747018752) }, { argument := 158939895356374526856970371072, coefficient := (-158939895356374526856970371072) }, { argument := 4179365474197620395399622688768, coefficient := (-4179365474197620395399622688768) }, { argument := 156933682958724049741545472, coefficient := (-156933682958724049741545472) }] }

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
def constantNumerator : ℤ := 315546480513349292661509108180975616
def positiveArguments : Array ℕ := #[
    5041, 31, 35, 15, 395, 35,
    15, 35, 35, 1451, 9, 395,
    1451, 31, 35, 9, 35, 3,
    87, 77, 5, 3, 5, 153,
    5, 3, 2451, 157, 87, 153,
    5, 157, 5, 153, 5, 3,
    159
  ]
def positiveCoefficients : Array ℕ := #[
    3195113337875252206472440429150208, 1199254413057712141308526592, 1353996917968384675670917120, 1160568786830044007717928960, 15280822359928912768286064640, 1353996917968384675670917120,
    1160568786830044007717928960, 1353996917968384675670917120, 1353996917968384675670917120, 56132843656346461839957164032, 1392682544196052809261514752, 15280822359928912768286064640,
    56132843656346461839957164032, 1199254413057712141308526592, 1353996917968384675670917120, 1392682544196052809261514752, 1353996917968384675670917120, 232113757366008801543585792,
    3365649481807127622381993984, 5957586439060892572952035328, 193428131138340667952988160, 3713820117856140824697372672, 193428131138340667952988160, 5918900812833224439361437696,
    6189700196426901374495621120, 3713820117856140824697372672, 94818469884014595430554796032, 6073643317743896973723828224, 3365649481807127622381993984, 5918900812833224439361437696,
    193428131138340667952988160, 6073643317743896973723828224, 193428131138340667952988160, 5918900812833224439361437696, 6189700196426901374495621120, 232113757366008801543585792,
    12302029140398466481810046976
  ]
def positiveScales : Array ℕ := #[
    12, 4, 5, 3, 8, 5,
    3, 5, 5, 10, 3, 8,
    10, 4, 5, 3, 5, 1,
    6, 6, 2, 1, 2, 7,
    2, 1, 11, 7, 6, 7,
    2, 7, 2, 7, 2, 1,
    7
  ]
def negativeArguments : Array ℕ := #[
    3712022085356773, 2077, 1445567833, 8369, 150891321, 1099321937,
    301782845, 8450176075, 2345, 8450182069, 2345, 317,
    8452174923, 603, 8452180917, 603, 8217, 317,
    9356145415, 2345, 9356152057, 2345, 8369, 1047,
    4696997, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    4179365320100953594815003492352, 156933682958724049741545472, 6826501083273704653041348640768, 161880002949677305009855791104, 695863395357738903413981184, 2534863803306706882237825024,
    695863863443869773793853440, 19484779429163561195562598400, 177183190437269088417873920, 19484793250386558422444146688, 177183190437269088417873920, 6131671757085399174109724672,
    19489388458850841969291165696, 182245567306905348086956032, 19489402280073839196172713984, 182245567306905348086956032, 158939895356374526856970371072, 6131671757085399174109724672,
    21573802498364505424218030080, 177183190437269088417873920, 21573817813773772621573259264, 177183190437269088417873920, 161880002949677305009855791104, 162015402641474143477422882816,
    44361882405878549919588941824, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    51, 11, 30, 13, 27, 30,
    28, 32, 11, 32, 11, 8,
    32, 9, 32, 9, 13, 8,
    33, 11, 33, 11, 13, 10,
    22, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12299494239009363, 4954196309696329, 5129283016944966, 3906890595303263, 8625708843063759, 5129283016944966,
    3906890595303263, 5129283016944966, 5129283016944966, 10502831804066725, 3169925001442312, 8625708843063759,
    10502831804066725, 4954196309696329, 5129283016944966, 3169925001442312, 5129283016944966, 1584962500720924,
    6442943495848725, 6266786540694901, 2321928094887362, 1584962500720924, 2321928094887362, 7257387842692651,
    2321928094887362, 1584962500720924, 11259154768866839, 7294620748891626, 6442943495848725, 7257387842692651,
    2321928094887362, 7294620748891626, 2321928094887362, 7257387842692651, 2321928094887362, 1584962500720924,
    7312882955284355
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    51721126717498483, 11020285500844648, 30428989162584425, 13030839532141380, 27168934586101003, 30033966796141026,
    28168935556557729, 32976334273057804, 11195372207402739, 32976335296410834, 11195372207402739, 8308339030139408,
    32976675495278989, 9236014191900085, 32976676518390009, 9236014191900085, 13004396051426535, 8308339030139408,
    33123267138492877, 11195372207402739, 33123268162672882, 11195372207402739, 13030839532141380, 10032045726930809,
    22163307241462242, 0, 0
  ]

abbrev PositiveTerm := Fin 37
abbrev NegativeTerm := Fin 27
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
noncomputable def positiveFloor : ℝ := 118268020717 / 250000000000
noncomputable def negativeCeiling : ℝ := 526029917 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4179365320100953594815003492352, coefficient := (-4179365320100953594815003492352) }, { argument := 156933682958724049741545472, coefficient := (-156933682958724049741545472) }, { argument := 6826501083273704653041348640768, coefficient := (-6826501083273704653041348640768) }, { argument := 161880002949677305009855791104, coefficient := (-161880002949677305009855791104) }, { argument := 695863395357738903413981184, coefficient := (-695863395357738903413981184) }, { argument := 2534863803306706882237825024, coefficient := (-2534863803306706882237825024) }, { argument := 695863863443869773793853440, coefficient := (-695863863443869773793853440) }, { argument := 19484779429163561195562598400, coefficient := (-19484779429163561195562598400) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 19484793250386558422444146688, coefficient := (-19484793250386558422444146688) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 6131671757085399174109724672, coefficient := (-6131671757085399174109724672) }, { argument := 19489388458850841969291165696, coefficient := (-19489388458850841969291165696) }, { argument := 182245567306905348086956032, coefficient := (-182245567306905348086956032) }, { argument := 19489402280073839196172713984, coefficient := (-19489402280073839196172713984) }, { argument := 182245567306905348086956032, coefficient := (-182245567306905348086956032) }, { argument := 158939895356374526856970371072, coefficient := (-158939895356374526856970371072) }, { argument := 6131671757085399174109724672, coefficient := (-6131671757085399174109724672) }, { argument := 21573802498364505424218030080, coefficient := (-21573802498364505424218030080) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 21573817813773772621573259264, coefficient := (-21573817813773772621573259264) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 161880002949677305009855791104, coefficient := (-161880002949677305009855791104) }, { argument := 162015402641474143477422882816, coefficient := (-162015402641474143477422882816) }, { argument := 44361882405878549919588941824, coefficient := (-44361882405878549919588941824) }, { argument := 3195113337875252206472440429150208, coefficient := 3195113337875252206472440429150208 }, { argument := 1199254413057712141308526592, coefficient := 1199254413057712141308526592 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 15280822359928912768286064640, coefficient := 15280822359928912768286064640 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 56132843656346461839957164032, coefficient := 56132843656346461839957164032 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 15280822359928912768286064640, coefficient := 15280822359928912768286064640 }, { argument := 56132843656346461839957164032, coefficient := 56132843656346461839957164032 }, { argument := 1199254413057712141308526592, coefficient := 1199254413057712141308526592 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 5957586439060892572952035328, coefficient := 5957586439060892572952035328 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 6189700196426901374495621120, coefficient := 6189700196426901374495621120 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 94818469884014595430554796032, coefficient := 94818469884014595430554796032 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 6073643317743896973723828224, coefficient := 6073643317743896973723828224 }, { argument := 193428131138340667952988160, coefficient := 193428131138340667952988160 }, { argument := 5918900812833224439361437696, coefficient := 5918900812833224439361437696 }, { argument := 6189700196426901374495621120, coefficient := 6189700196426901374495621120 }, { argument := 232113757366008801543585792, coefficient := 232113757366008801543585792 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 12302029140398466481810046976, coefficient := 12302029140398466481810046976 }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk17
