import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 15, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15

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
def constantNumerator : ℤ := (-10589401102843286409599177302474752)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1626123, 1113, 8657909, 483, 93, 1929,
    969, 1626123, 1113, 93, 209133069290555, 10842025984373701,
    2095, 4903, 60067, 64667, 5421012389255407, 60067,
    2095, 4087, 4077, 4087, 64667, 4077,
    104567137576721, 4903, 367073941406639, 48035641355375227, 13954957821, 484279293856092281,
    460181733, 1073410737, 13954957821, 13953183741, 460181733, 172228510773,
    6900059835, 24017821650792759, 13954957821, 1073410737, 6900059835, 1073410737,
    13954984701, 13953183741, 377107242170095, 5607, 9345, 285957,
    9345, 293433, 9345, 285957, 162603, 293433,
    4580919, 5607, 9345, 285957, 9345, 5607,
    9345, 143913, 162603, 5607
  ]
def negativeCoefficients : Array ℕ := #[
    30716595008893744335323922432, 86114203982789265372670328832, 327086554186683576979724173312, 74740629871854834097034625024, 3597763239173136423925579776, 74624572993171829696262832128,
    74972743629220842898578210816, 30716595008893744335323922432, 86114203982789265372670328832, 3597763239173136423925579776, 235462903231947904565714616320, 12207036045791658727829011431424,
    81046386946964739872302039040, 94837812697128429497350094848, 1161864755308670890193213980672, 2501683391264615194903177068544, 12207034688110746589551380135936, 1161864755308670890193213980672,
    81046386946964739872302039040, 79054077196239830992386260992, 78860649065101490324433272832, 79054077196239830992386260992, 2501683391264615194903177068544, 78860649065101490324433272832,
    235464260912860042843345911808, 94837812697128429497350094848, 103322129108522417669940445184, 13520831031785666233865089318912, 514847070966797015612204777472, 136312502959596508102855372046336,
    271643348993508518441722576896, 19800933151410952124070100992, 514847070966797015612204777472, 514781618967344442329542950912, 271643348993508518441722576896, 6354110520851318833138511118336,
    509134551478110226245683773440, 13520831579595162567129125879808, 514847070966797015612204777472, 19800933151410952124070100992, 509134551478110226245683773440, 19800933151410952124070100992,
    514848062663758418237699653632, 514781618967344442329542950912, 106146252207247202334351032320, 105913235477800402852773888, 2824352946074677409407303680, 2700787504683910272745734144,
    88261029564833669043978240, 2771396328335777207980916736, 88261029564833669043978240, 2700787504683910272745734144, 1535741914428105841365221376, 2771396328335777207980916736,
    43265556692681464565358133248, 1694611767644806445644382208, 2824352946074677409407303680, 2700787504683910272745734144, 88261029564833669043978240, 1694611767644806445644382208,
    88261029564833669043978240, 2718439710596877006554529792, 1535741914428105841365221376, 105913235477800402852773888
  ]
def negativeScales : Array ℕ := #[
    20, 10, 23, 8, 6, 10,
    9, 20, 10, 6, 47, 53,
    11, 12, 15, 15, 52, 15,
    11, 11, 11, 11, 15, 11,
    46, 12, 48, 55, 33, 58,
    28, 29, 33, 33, 28, 37,
    32, 54, 33, 29, 32, 29,
    33, 33, 48, 12, 13, 18,
    13, 18, 13, 18, 17, 18,
    22, 12, 13, 18, 13, 12,
    13, 17, 17, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    20633004956381019, 10120237877341960, 23045587206333363, 8915879384625971, 6539158811108986, 10913637433615165,
    9920352861677847, 20633004956381019, 10120237877341960, 6539158811108986, 47571414535399904, 53267483887850979,
    11032734528586714, 12259449046285686, 15874284993655798, 15980742080039423, 52267483727392731, 15874284993655798,
    11032734528586714, 11996826550526844, 11993292262754870, 11996826550526844, 15980742080039423, 11993292262754870,
    46571422853966631, 12259449046285686, 48383064029518657, 55414954768319942, 33700058712796449, 58748616932803377,
    28777628476154460, 29999555101629229, 33700058712796449, 33699875292741748, 28777628476154460, 37325533030549743,
    32683961726547270, 54414954826772121, 33700058712796449, 29999555101629229, 32683961726547270, 29999555101629229,
    33700061491708855, 33699875292741748, 48421968185459425, 12453013354466367, 13189978948632521, 18125438696437810,
    13189978948632521, 18162671602636786, 13189978948632521, 18125438696437810, 17310994349593887, 18162671602636786,
    22127205622611998, 12453013354466367, 13189978948632521, 18125438696437810, 13189978948632521, 12453013354466367,
    13189978948632521, 17134837394440060, 17310994349593887, 12453013354466367
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
noncomputable def negativeCeiling : ℝ := 68278426593 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 30716595008893744335323922432, coefficient := (-30716595008893744335323922432) }, { argument := 86114203982789265372670328832, coefficient := (-86114203982789265372670328832) }, { argument := 327086554186683576979724173312, coefficient := (-327086554186683576979724173312) }, { argument := 74740629871854834097034625024, coefficient := (-74740629871854834097034625024) }, { argument := 3597763239173136423925579776, coefficient := (-3597763239173136423925579776) }, { argument := 74624572993171829696262832128, coefficient := (-74624572993171829696262832128) }, { argument := 74972743629220842898578210816, coefficient := (-74972743629220842898578210816) }, { argument := 30716595008893744335323922432, coefficient := (-30716595008893744335323922432) }, { argument := 86114203982789265372670328832, coefficient := (-86114203982789265372670328832) }, { argument := 3597763239173136423925579776, coefficient := (-3597763239173136423925579776) }, { argument := 235462903231947904565714616320, coefficient := (-235462903231947904565714616320) }, { argument := 12207036045791658727829011431424, coefficient := (-12207036045791658727829011431424) }, { argument := 81046386946964739872302039040, coefficient := (-81046386946964739872302039040) }, { argument := 94837812697128429497350094848, coefficient := (-94837812697128429497350094848) }, { argument := 1161864755308670890193213980672, coefficient := (-1161864755308670890193213980672) }, { argument := 2501683391264615194903177068544, coefficient := (-2501683391264615194903177068544) }, { argument := 12207034688110746589551380135936, coefficient := (-12207034688110746589551380135936) }, { argument := 1161864755308670890193213980672, coefficient := (-1161864755308670890193213980672) }, { argument := 81046386946964739872302039040, coefficient := (-81046386946964739872302039040) }, { argument := 79054077196239830992386260992, coefficient := (-79054077196239830992386260992) }, { argument := 78860649065101490324433272832, coefficient := (-78860649065101490324433272832) }, { argument := 79054077196239830992386260992, coefficient := (-79054077196239830992386260992) }, { argument := 2501683391264615194903177068544, coefficient := (-2501683391264615194903177068544) }, { argument := 78860649065101490324433272832, coefficient := (-78860649065101490324433272832) }, { argument := 235464260912860042843345911808, coefficient := (-235464260912860042843345911808) }, { argument := 94837812697128429497350094848, coefficient := (-94837812697128429497350094848) }, { argument := 103322129108522417669940445184, coefficient := (-103322129108522417669940445184) }, { argument := 13520831031785666233865089318912, coefficient := (-13520831031785666233865089318912) }, { argument := 514847070966797015612204777472, coefficient := (-514847070966797015612204777472) }, { argument := 136312502959596508102855372046336, coefficient := (-136312502959596508102855372046336) }, { argument := 271643348993508518441722576896, coefficient := (-271643348993508518441722576896) }, { argument := 19800933151410952124070100992, coefficient := (-19800933151410952124070100992) }, { argument := 514847070966797015612204777472, coefficient := (-514847070966797015612204777472) }, { argument := 514781618967344442329542950912, coefficient := (-514781618967344442329542950912) }, { argument := 271643348993508518441722576896, coefficient := (-271643348993508518441722576896) }, { argument := 6354110520851318833138511118336, coefficient := (-6354110520851318833138511118336) }, { argument := 509134551478110226245683773440, coefficient := (-509134551478110226245683773440) }, { argument := 13520831579595162567129125879808, coefficient := (-13520831579595162567129125879808) }, { argument := 514847070966797015612204777472, coefficient := (-514847070966797015612204777472) }, { argument := 19800933151410952124070100992, coefficient := (-19800933151410952124070100992) }, { argument := 509134551478110226245683773440, coefficient := (-509134551478110226245683773440) }, { argument := 19800933151410952124070100992, coefficient := (-19800933151410952124070100992) }, { argument := 514848062663758418237699653632, coefficient := (-514848062663758418237699653632) }, { argument := 514781618967344442329542950912, coefficient := (-514781618967344442329542950912) }, { argument := 106146252207247202334351032320, coefficient := (-106146252207247202334351032320) }, { argument := 105913235477800402852773888, coefficient := (-105913235477800402852773888) }, { argument := 2824352946074677409407303680, coefficient := (-2824352946074677409407303680) }, { argument := 2700787504683910272745734144, coefficient := (-2700787504683910272745734144) }, { argument := 88261029564833669043978240, coefficient := (-88261029564833669043978240) }, { argument := 2771396328335777207980916736, coefficient := (-2771396328335777207980916736) }, { argument := 88261029564833669043978240, coefficient := (-88261029564833669043978240) }, { argument := 2700787504683910272745734144, coefficient := (-2700787504683910272745734144) }, { argument := 1535741914428105841365221376, coefficient := (-1535741914428105841365221376) }, { argument := 2771396328335777207980916736, coefficient := (-2771396328335777207980916736) }, { argument := 43265556692681464565358133248, coefficient := (-43265556692681464565358133248) }, { argument := 1694611767644806445644382208, coefficient := (-1694611767644806445644382208) }, { argument := 2824352946074677409407303680, coefficient := (-2824352946074677409407303680) }, { argument := 2700787504683910272745734144, coefficient := (-2700787504683910272745734144) }, { argument := 88261029564833669043978240, coefficient := (-88261029564833669043978240) }, { argument := 1694611767644806445644382208, coefficient := (-1694611767644806445644382208) }, { argument := 88261029564833669043978240, coefficient := (-88261029564833669043978240) }, { argument := 2718439710596877006554529792, coefficient := (-2718439710596877006554529792) }, { argument := 1535741914428105841365221376, coefficient := (-1535741914428105841365221376) }, { argument := 105913235477800402852773888, coefficient := (-105913235477800402852773888) }] }

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
def constantNumerator : ℤ := (-3564737160426318886756686474772480)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    21118242783199, 827966249, 777580432802721, 13029574129, 392194539, 388773482199497,
    392194539, 392194539, 33597998841, 392194539, 13029574129, 33597998841,
    10575856388087, 392194539, 392194539, 827966249, 315, 525,
    16065, 525, 16485, 525, 16065, 9135,
    16485, 257355, 315, 525, 16065, 525,
    315, 525, 8085, 9135, 315, 429479819,
    7515361441, 7515365127, 429476133, 368856404329535, 5607, 315,
    1303115820594259, 17031, 184428198020023, 17031, 17031, 5607,
    315, 209133021279173, 10842021947132987, 2095, 4903, 60067,
    64667, 5421010370635537, 60067, 2095, 4087, 4077,
    4087, 64667, 4077, 104567113570543
  ]
def negativeCoefficients : Array ℕ := #[
    380432441316538730979908386816, 3818320374243069241742852096, 14007643789683693200866975678464, 30044152418386255349502967808, 3617356144019749807966912512, 14007040876521478790788830724096,
    3617356144019749807966912512, 3617356144019749807966912512, 154943421502179283441249419264, 3617356144019749807966912512, 30044152418386255349502967808, 154943421502179283441249419264,
    381035383108099943455277449216, 3617356144019749807966912512, 3617356144019749807966912512, 3818320374243069241742852096, 5950181768415752969256960, 158671513824420079180185600,
    151729635094601700716052480, 4958484807013127474380800, 155696422940212202695557120, 4958484807013127474380800, 151729635094601700716052480, 86277635642028418054225920,
    155696422940212202695557120, 2430649252397835087941468160, 95202908294652047508111360, 158671513824420079180185600, 151729635094601700716052480, 4958484807013127474380800,
    95202908294652047508111360, 4958484807013127474380800, 152721332056004326210928640, 86277635642028418054225920, 5950181768415752969256960, 3961252152958050443305418752,
    138633949123552026048285638656, 138634017118250681741692895232, 3961218155608722596601790464, 103823847818232177091370024960, 105913235477800402852773888, 5950181768415752969256960,
    366794495253056434363017723904, 160853247139505855268913152, 103823845484948453873130930176, 160853247139505855268913152, 160853247139505855268913152, 105913235477800402852773888,
    5950181768415752969256960, 235462849175937383380079869952, 12207031500262714933980208037888, 81046386946964739872302039040, 94837812697128429497350094848, 1161864755308670890193213980672,
    2501683391264615194903177068544, 12207030142582899422211841458176, 1161864755308670890193213980672, 81046386946964739872302039040, 79054077196239830992386260992, 78860649065101490324433272832,
    79054077196239830992386260992, 2501683391264615194903177068544, 78860649065101490324433272832, 235464206855752895148446449664
  ]
def negativeScales : Array ℕ := #[
    44, 29, 49, 33, 28, 48,
    28, 28, 34, 28, 33, 34,
    43, 28, 28, 29, 8, 9,
    13, 9, 14, 9, 13, 13,
    14, 17, 8, 9, 13, 9,
    8, 9, 12, 13, 8, 28,
    32, 32, 28, 48, 12, 8,
    50, 14, 47, 14, 14, 12,
    8, 47, 53, 11, 12, 15,
    15, 52, 15, 11, 11, 11,
    11, 15, 11, 46
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    44263555028770254, 29624996718389274, 49465985243542697, 33601070879138489, 28546994206378086, 48465923146122025,
    28546994206378086, 28546994206378086, 34967656268851729, 28546994206378086, 33601070879138489, 34967656268851729,
    43265839724949190, 28546994206378086, 28546994206378086, 29624996718389274, 8299208018387279, 9036173612553486,
    13971633375310864, 9036173612553486, 14008866266557750, 9036173612553486, 13971633375310864, 13157189013514852,
    14008866266557750, 17973400301926033, 8299208018387279, 9036173612553486, 13971633375310864, 9036173612553486,
    8299208018387279, 9036173612553486, 12981032075801390, 13157189013514852, 8299208018387279, 28678015100720415,
    32807195344983114, 32807196052570199, 28678002718772507, 48390052613323854, 12453013354466367, 8299208018387279,
    50210886739274138, 14055875526996034, 47390052580901468, 14055875526996034, 14055875526996034, 12453013354466367,
    8299208018387279, 47571414204195514, 53267483350635126, 11032734528586714, 12259449046285686, 15874284993655798,
    15980742080039423, 52267483190176947, 15874284993655798, 11032734528586714, 11996826550526844, 11993292262754870,
    11996826550526844, 15980742080039423, 11993292262754870, 46571422522757431
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
noncomputable def negativeCeiling : ℝ := 17396986017 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 380432441316538730979908386816, coefficient := (-380432441316538730979908386816) }, { argument := 3818320374243069241742852096, coefficient := (-3818320374243069241742852096) }, { argument := 14007643789683693200866975678464, coefficient := (-14007643789683693200866975678464) }, { argument := 30044152418386255349502967808, coefficient := (-30044152418386255349502967808) }, { argument := 3617356144019749807966912512, coefficient := (-3617356144019749807966912512) }, { argument := 14007040876521478790788830724096, coefficient := (-14007040876521478790788830724096) }, { argument := 3617356144019749807966912512, coefficient := (-3617356144019749807966912512) }, { argument := 3617356144019749807966912512, coefficient := (-3617356144019749807966912512) }, { argument := 154943421502179283441249419264, coefficient := (-154943421502179283441249419264) }, { argument := 3617356144019749807966912512, coefficient := (-3617356144019749807966912512) }, { argument := 30044152418386255349502967808, coefficient := (-30044152418386255349502967808) }, { argument := 154943421502179283441249419264, coefficient := (-154943421502179283441249419264) }, { argument := 381035383108099943455277449216, coefficient := (-381035383108099943455277449216) }, { argument := 3617356144019749807966912512, coefficient := (-3617356144019749807966912512) }, { argument := 3617356144019749807966912512, coefficient := (-3617356144019749807966912512) }, { argument := 3818320374243069241742852096, coefficient := (-3818320374243069241742852096) }, { argument := 5950181768415752969256960, coefficient := (-5950181768415752969256960) }, { argument := 158671513824420079180185600, coefficient := (-158671513824420079180185600) }, { argument := 151729635094601700716052480, coefficient := (-151729635094601700716052480) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 155696422940212202695557120, coefficient := (-155696422940212202695557120) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 151729635094601700716052480, coefficient := (-151729635094601700716052480) }, { argument := 86277635642028418054225920, coefficient := (-86277635642028418054225920) }, { argument := 155696422940212202695557120, coefficient := (-155696422940212202695557120) }, { argument := 2430649252397835087941468160, coefficient := (-2430649252397835087941468160) }, { argument := 95202908294652047508111360, coefficient := (-95202908294652047508111360) }, { argument := 158671513824420079180185600, coefficient := (-158671513824420079180185600) }, { argument := 151729635094601700716052480, coefficient := (-151729635094601700716052480) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 95202908294652047508111360, coefficient := (-95202908294652047508111360) }, { argument := 4958484807013127474380800, coefficient := (-4958484807013127474380800) }, { argument := 152721332056004326210928640, coefficient := (-152721332056004326210928640) }, { argument := 86277635642028418054225920, coefficient := (-86277635642028418054225920) }, { argument := 5950181768415752969256960, coefficient := (-5950181768415752969256960) }, { argument := 3961252152958050443305418752, coefficient := (-3961252152958050443305418752) }, { argument := 138633949123552026048285638656, coefficient := (-138633949123552026048285638656) }, { argument := 138634017118250681741692895232, coefficient := (-138634017118250681741692895232) }, { argument := 3961218155608722596601790464, coefficient := (-3961218155608722596601790464) }, { argument := 103823847818232177091370024960, coefficient := (-103823847818232177091370024960) }, { argument := 105913235477800402852773888, coefficient := (-105913235477800402852773888) }, { argument := 5950181768415752969256960, coefficient := (-5950181768415752969256960) }, { argument := 366794495253056434363017723904, coefficient := (-366794495253056434363017723904) }, { argument := 160853247139505855268913152, coefficient := (-160853247139505855268913152) }, { argument := 103823845484948453873130930176, coefficient := (-103823845484948453873130930176) }, { argument := 160853247139505855268913152, coefficient := (-160853247139505855268913152) }, { argument := 160853247139505855268913152, coefficient := (-160853247139505855268913152) }, { argument := 105913235477800402852773888, coefficient := (-105913235477800402852773888) }, { argument := 5950181768415752969256960, coefficient := (-5950181768415752969256960) }, { argument := 235462849175937383380079869952, coefficient := (-235462849175937383380079869952) }, { argument := 12207031500262714933980208037888, coefficient := (-12207031500262714933980208037888) }, { argument := 81046386946964739872302039040, coefficient := (-81046386946964739872302039040) }, { argument := 94837812697128429497350094848, coefficient := (-94837812697128429497350094848) }, { argument := 1161864755308670890193213980672, coefficient := (-1161864755308670890193213980672) }, { argument := 2501683391264615194903177068544, coefficient := (-2501683391264615194903177068544) }, { argument := 12207030142582899422211841458176, coefficient := (-12207030142582899422211841458176) }, { argument := 1161864755308670890193213980672, coefficient := (-1161864755308670890193213980672) }, { argument := 81046386946964739872302039040, coefficient := (-81046386946964739872302039040) }, { argument := 79054077196239830992386260992, coefficient := (-79054077196239830992386260992) }, { argument := 78860649065101490324433272832, coefficient := (-78860649065101490324433272832) }, { argument := 79054077196239830992386260992, coefficient := (-79054077196239830992386260992) }, { argument := 2501683391264615194903177068544, coefficient := (-2501683391264615194903177068544) }, { argument := 78860649065101490324433272832, coefficient := (-78860649065101490324433272832) }, { argument := 235464206855752895148446449664, coefficient := (-235464206855752895148446449664) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15
