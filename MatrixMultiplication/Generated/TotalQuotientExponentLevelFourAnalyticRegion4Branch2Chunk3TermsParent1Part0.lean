import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 3, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk3

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-141707025995976144631489749843968)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1074775070065, 49706625003231, 6211975661419, 135182137355, 65188236367, 4261128758797,
    51405868968419, 4261150573611, 137086047047, 65188236367, 2369235462333, 4738473975693,
    130376119899, 3806229836825, 44021031302819, 176045690928773, 1915097536875, 2369235462333,
    155168304186129, 1871555481858063, 155169205117857, 4972069689285, 4261128758797, 155168304186129,
    19396050785127, 2130560015829, 1074775070065, 3806229836825, 537746987835, 537746987835,
    49739102566037, 49728277349923, 541088007785, 4738473975693, 19396050785127, 116972295682887,
    155169307212993, 2486036498949, 51405868968419, 1871555481858063, 116972295682887, 25702884858063,
    49706625003231, 44021031302819, 49739102566037, 130376119899, 2130560015829, 25702884858063,
    4261141846899, 68542832757, 4261150573611, 155169205117857, 155169307212993, 4261141846899,
    6211975661419, 176045690928773, 49728277349923, 137086047047, 4972069689285, 2486036498949,
    68542832757, 135182137355, 1915097536875, 541088007785
  ]
def negativeCoefficients : Array ℕ := #[
    302522287815739545632112640, 13991171115149756945752129536, 13988125637000599412683046912, 304403111709562603873239040, 36697714626420126991253504, 1199401118143492083083640832,
    14469465770676772000564772864, 1199407258467754680376098816, 38586291899910217722232832, 36697714626420126991253504, 1333760993164482951455440896, 1333761851952236720038084608,
    36697615312196719286943744, 1071358454675720862118707200, 49563275042960147115520557056, 49552456754187724417126105088, 1078104069181050590330880000, 1333760993164482951455440896,
    43675994807022646187601690624, 526796035668698850846811619328, 43676248396759802878667784192, 1399513199995253989268520960, 1199401118143492083083640832, 43675994807022646187601690624,
    43676023544178586789657706496, 1199398661672245307425947648, 302522287815739545632112640, 1071358454675720862118707200, 302724641754164080693739520, 302724641754164080693739520,
    14000312736384194663281590272, 13997265708930618695234879488, 304605468779396254840913920, 1333761851952236720038084608, 43676023544178586789657706496, 526796387250121371144475901952,
    43676277133985830749924753408, 1399514131287021108842201088, 14469465770676772000564772864, 526796035668698850846811619328, 526796387250121371144475901952, 14469437833639911346359238656,
    13991171115149756945752129536, 49563275042960147115520557056, 14000312736384194663281590272, 36697615312196719286943744, 1199398661672245307425947648, 14469437833639911346359238656,
    1199404802116697719773855744, 38586184507917928375517184, 1199407258467754680376098816, 43676248396759802878667784192, 43676277133985830749924753408, 1199404802116697719773855744,
    13988125637000599412683046912, 49552456754187724417126105088, 13997265708930618695234879488, 38586291899910217722232832, 1399513199995253989268520960, 1399514131287021108842201088,
    38586184507917928375517184, 304403111709562603873239040, 1078104069181050590330880000, 304605468779396254840913920
  ]
def negativeScales : Array ℕ := #[
    39, 45, 42, 36, 35, 41,
    45, 41, 36, 35, 41, 42,
    36, 41, 45, 47, 40, 41,
    47, 50, 47, 42, 41, 47,
    44, 40, 39, 41, 38, 38,
    45, 45, 38, 42, 44, 46,
    47, 41, 45, 50, 46, 44,
    45, 45, 45, 36, 40, 44,
    41, 35, 41, 47, 47, 41,
    42, 47, 45, 36, 42, 41,
    35, 36, 40, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    39967171915371313, 45498503383559610, 42498189315891703, 36976113589789280, 35923892599958236, 41954372796051122,
    45546998313739578, 41954380181899129, 36996290803636364, 35923892599958236, 41107558724081416, 42107559653009793,
    36923888695618427, 41791499819677436, 45323258177902713, 47322943243202805, 40800555010502845, 41107558724081416,
    47140827220590661, 50733159240720102, 47140835597082043, 42176983656213581, 41954372796051122, 47140827220590661,
    44140828169829228, 40954369841290509, 39967171915371313, 41791499819677436, 38968136596355897, 38968136596355897,
    45499445711030320, 45499131688771380, 38977072327116705, 42107559653009793, 44140828169829228, 46733160203568288,
    47140836546317414, 41176984616239943, 45546998313739578, 50733159240720102, 46733160203568288, 44546995528241890,
    45498503383559610, 45323258177902713, 45499445711030320, 36923888695618427, 40954369841290509, 44546995528241890,
    41954377227298212, 35996286788371926, 41954380181899129, 47140835597082043, 47140836546317414, 41954377227298212,
    42498189315891703, 47322943243202805, 45499131688771380, 36996290803636364, 42176983656213581, 41176984616239943,
    35996286788371926, 36976113589789280, 40800555010502845, 38977072327116705
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
noncomputable def negativeCeiling : ℝ := 411778471 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 302522287815739545632112640, coefficient := (-302522287815739545632112640) }, { argument := 13991171115149756945752129536, coefficient := (-13991171115149756945752129536) }, { argument := 13988125637000599412683046912, coefficient := (-13988125637000599412683046912) }, { argument := 304403111709562603873239040, coefficient := (-304403111709562603873239040) }, { argument := 36697714626420126991253504, coefficient := (-36697714626420126991253504) }, { argument := 1199401118143492083083640832, coefficient := (-1199401118143492083083640832) }, { argument := 14469465770676772000564772864, coefficient := (-14469465770676772000564772864) }, { argument := 1199407258467754680376098816, coefficient := (-1199407258467754680376098816) }, { argument := 38586291899910217722232832, coefficient := (-38586291899910217722232832) }, { argument := 36697714626420126991253504, coefficient := (-36697714626420126991253504) }, { argument := 1333760993164482951455440896, coefficient := (-1333760993164482951455440896) }, { argument := 1333761851952236720038084608, coefficient := (-1333761851952236720038084608) }, { argument := 36697615312196719286943744, coefficient := (-36697615312196719286943744) }, { argument := 1071358454675720862118707200, coefficient := (-1071358454675720862118707200) }, { argument := 49563275042960147115520557056, coefficient := (-49563275042960147115520557056) }, { argument := 49552456754187724417126105088, coefficient := (-49552456754187724417126105088) }, { argument := 1078104069181050590330880000, coefficient := (-1078104069181050590330880000) }, { argument := 1333760993164482951455440896, coefficient := (-1333760993164482951455440896) }, { argument := 43675994807022646187601690624, coefficient := (-43675994807022646187601690624) }, { argument := 526796035668698850846811619328, coefficient := (-526796035668698850846811619328) }, { argument := 43676248396759802878667784192, coefficient := (-43676248396759802878667784192) }, { argument := 1399513199995253989268520960, coefficient := (-1399513199995253989268520960) }, { argument := 1199401118143492083083640832, coefficient := (-1199401118143492083083640832) }, { argument := 43675994807022646187601690624, coefficient := (-43675994807022646187601690624) }, { argument := 43676023544178586789657706496, coefficient := (-43676023544178586789657706496) }, { argument := 1199398661672245307425947648, coefficient := (-1199398661672245307425947648) }, { argument := 302522287815739545632112640, coefficient := (-302522287815739545632112640) }, { argument := 1071358454675720862118707200, coefficient := (-1071358454675720862118707200) }, { argument := 302724641754164080693739520, coefficient := (-302724641754164080693739520) }, { argument := 302724641754164080693739520, coefficient := (-302724641754164080693739520) }, { argument := 14000312736384194663281590272, coefficient := (-14000312736384194663281590272) }, { argument := 13997265708930618695234879488, coefficient := (-13997265708930618695234879488) }, { argument := 304605468779396254840913920, coefficient := (-304605468779396254840913920) }, { argument := 1333761851952236720038084608, coefficient := (-1333761851952236720038084608) }, { argument := 43676023544178586789657706496, coefficient := (-43676023544178586789657706496) }, { argument := 526796387250121371144475901952, coefficient := (-526796387250121371144475901952) }, { argument := 43676277133985830749924753408, coefficient := (-43676277133985830749924753408) }, { argument := 1399514131287021108842201088, coefficient := (-1399514131287021108842201088) }, { argument := 14469465770676772000564772864, coefficient := (-14469465770676772000564772864) }, { argument := 526796035668698850846811619328, coefficient := (-526796035668698850846811619328) }, { argument := 526796387250121371144475901952, coefficient := (-526796387250121371144475901952) }, { argument := 14469437833639911346359238656, coefficient := (-14469437833639911346359238656) }, { argument := 13991171115149756945752129536, coefficient := (-13991171115149756945752129536) }, { argument := 49563275042960147115520557056, coefficient := (-49563275042960147115520557056) }, { argument := 14000312736384194663281590272, coefficient := (-14000312736384194663281590272) }, { argument := 36697615312196719286943744, coefficient := (-36697615312196719286943744) }, { argument := 1199398661672245307425947648, coefficient := (-1199398661672245307425947648) }, { argument := 14469437833639911346359238656, coefficient := (-14469437833639911346359238656) }, { argument := 1199404802116697719773855744, coefficient := (-1199404802116697719773855744) }, { argument := 38586184507917928375517184, coefficient := (-38586184507917928375517184) }, { argument := 1199407258467754680376098816, coefficient := (-1199407258467754680376098816) }, { argument := 43676248396759802878667784192, coefficient := (-43676248396759802878667784192) }, { argument := 43676277133985830749924753408, coefficient := (-43676277133985830749924753408) }, { argument := 1199404802116697719773855744, coefficient := (-1199404802116697719773855744) }, { argument := 13988125637000599412683046912, coefficient := (-13988125637000599412683046912) }, { argument := 49552456754187724417126105088, coefficient := (-49552456754187724417126105088) }, { argument := 13997265708930618695234879488, coefficient := (-13997265708930618695234879488) }, { argument := 38586291899910217722232832, coefficient := (-38586291899910217722232832) }, { argument := 1399513199995253989268520960, coefficient := (-1399513199995253989268520960) }, { argument := 1399514131287021108842201088, coefficient := (-1399514131287021108842201088) }, { argument := 38586184507917928375517184, coefficient := (-38586184507917928375517184) }, { argument := 304403111709562603873239040, coefficient := (-304403111709562603873239040) }, { argument := 1078104069181050590330880000, coefficient := (-1078104069181050590330880000) }, { argument := 304605468779396254840913920, coefficient := (-304605468779396254840913920) }] }

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


end Parent1

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 123306412996758126535573592080384
def positiveArguments : Array ℕ := #[
    9, 756671, 21443739, 6057325, 1793969, 65314875,
    130629837, 3587931, 145103, 19005475, 229234925, 19005585,
    609059, 355035, 16422859, 8209639, 89315
  ]
def positiveCoefficients : Array ℕ := #[
    2852213850513516153367582212096, 57172444303351317015881056256, 202530388642009285970192498688, 57209817111696747388102246400, 33887116307628698217475997696, 1233763106131282073707610112000,
    1233763927823050093025877295104, 33887050194497938042443005952, 5481836350110673035543445504, 179501636262033940735537971200, 2165062653046273810676423065600, 179502675182660172057484984320,
    5752399615380206488416944128, 3353210768491248976889118720, 155109517788988197449108553728, 155075696200237885050088062976, 3374225299340018898090065920
  ]
def positiveScales : Array ℕ := #[
    3, 19, 24, 22, 20, 25,
    26, 21, 17, 24, 27, 24,
    19, 18, 23, 22, 16
  ]
def negativeArguments : Array ℕ := #[
    1, 1, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    316912650057057350374175801344, 2535301200456458802993406410752, 2535301200456458802993406410752, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    0, 0, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 19529306628225696, 24354053144935030, 22530249389218801, 20774723529829279, 25960908256203934,
    26960909217044977, 21774720715155466, 17146717821824796, 24179911746847921, 27772251621172212, 24179920096862601,
    19216222464283539, 18437601729582122, 23969201966206902, 22968887352642833, 16446614868538854
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0, 0, 0
  ]

abbrev PositiveTerm := Fin 17
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 480053371 / 250000000000
noncomputable def negativeCeiling : ℝ := 0 / 1

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2852213850513516153367582212096, coefficient := 2852213850513516153367582212096 }, { argument := 57172444303351317015881056256, coefficient := 57172444303351317015881056256 }, { argument := 202530388642009285970192498688, coefficient := 202530388642009285970192498688 }, { argument := 57209817111696747388102246400, coefficient := 57209817111696747388102246400 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 33887116307628698217475997696, coefficient := 33887116307628698217475997696 }, { argument := 1233763106131282073707610112000, coefficient := 1233763106131282073707610112000 }, { argument := 1233763927823050093025877295104, coefficient := 1233763927823050093025877295104 }, { argument := 33887050194497938042443005952, coefficient := 33887050194497938042443005952 }, { argument := 2535301200456458802993406410752, coefficient := (-2535301200456458802993406410752) }, { argument := 5481836350110673035543445504, coefficient := 5481836350110673035543445504 }, { argument := 179501636262033940735537971200, coefficient := 179501636262033940735537971200 }, { argument := 2165062653046273810676423065600, coefficient := 2165062653046273810676423065600 }, { argument := 179502675182660172057484984320, coefficient := 179502675182660172057484984320 }, { argument := 5752399615380206488416944128, coefficient := 5752399615380206488416944128 }, { argument := 2535301200456458802993406410752, coefficient := (-2535301200456458802993406410752) }, { argument := 3353210768491248976889118720, coefficient := 3353210768491248976889118720 }, { argument := 155109517788988197449108553728, coefficient := 155109517788988197449108553728 }, { argument := 155075696200237885050088062976, coefficient := 155075696200237885050088062976 }, { argument := 3374225299340018898090065920, coefficient := 3374225299340018898090065920 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk3
