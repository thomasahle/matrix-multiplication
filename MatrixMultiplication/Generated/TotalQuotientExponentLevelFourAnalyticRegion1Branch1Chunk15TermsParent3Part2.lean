import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 15, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15

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
def constantNumerator : ℤ := (-1116919111713646169337649390682112)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2795, 145, 750638567, 7502597659, 15005191651, 750638567,
    17054039249, 105, 87, 61211110843, 585, 4264748381,
    2343, 2343, 1677, 87, 34596474944611497, 34596470547159895,
    2046397547, 175, 145, 7343711449, 975, 511748015,
    3905, 3905, 2795, 145, 7607417987, 7607419773,
    2082077, 2343, 67947, 60137, 3905, 2343,
    3905, 119493, 3905, 2343, 1914231, 122617,
    67947, 119493, 3905, 122617, 3905, 119493,
    3905, 2343, 1461769841, 14610321757, 29220636373, 1461769841,
    2343, 67947, 60137, 3905, 2343, 3905,
    119493, 3905, 2343, 1914231
  ]
def negativeCoefficients : Array ℕ := #[
    105592114556965266978242560, 5477945120128788447887360, 3461709384326270049811693568, 138398498903585405400141266944, 138398465081480146253678379008, 3461709384326270049811693568,
    314591497449300842285455376384, 2030995376952577013506375680, 105176546306472738199437312, 1129145696188288726154805772288, 2828886417898232268812451840, 314682887692296619674287734784,
    2832513195357076156336570368, 2832513195357076156336570368, 2027368599493733125982257152, 105176546306472738199437312, 9738041979305314945636900012032, 9738040741532727686449982341120,
    18874685911288006808726142976, 105781009216280052786790400, 5477945120128788447887360, 67733782825436867051537825792, 147337834265532930667315200, 18880169325867753452056084480,
    147526728924847716475863040, 147526728924847716475863040, 105592114556965266978242560, 5477945120128788447887360, 70166046333961848388631658496, 70166062806904306211261251584,
    9832330639553782297596526592, 177032074709817259771035648, 2566965083292350266680016896, 4543823250885309667456581632, 147526728924847716475863040, 2832513195357076156336570368,
    147526728924847716475863040, 4514317905100340124161409024, 4720855325595126927227617280, 2832513195357076156336570368, 72317602518960350616468062208, 4632339288240218297342099456,
    2566965083292350266680016896, 4514317905100340124161409024, 147526728924847716475863040, 4632339288240218297342099456, 147526728924847716475863040, 4514317905100340124161409024,
    4720855325595126927227617280, 177032074709817259771035648, 3370611768949262943237701632, 134756433142964736836979654656, 134756400210914879247002632192, 3370611768949262943237701632,
    177032074709817259771035648, 2566965083292350266680016896, 4543823250885309667456581632, 147526728924847716475863040, 2832513195357076156336570368, 147526728924847716475863040,
    4514317905100340124161409024, 4720855325595126927227617280, 2832513195357076156336570368, 72317602518960350616468062208
  ]
def negativeScales : Array ℕ := #[
    11, 7, 29, 32, 33, 29,
    33, 6, 6, 35, 9, 31,
    11, 11, 10, 6, 54, 54,
    30, 7, 7, 32, 9, 28,
    11, 11, 11, 7, 32, 32,
    20, 11, 16, 15, 11, 11,
    11, 16, 11, 11, 20, 16,
    16, 16, 11, 16, 11, 16,
    11, 11, 30, 33, 34, 30,
    11, 16, 15, 11, 11, 11,
    16, 11, 11, 20
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11448632567730597, 7179909090014935, 29483543175343454, 32804743047759886, 33804742695191104, 29483543175343454,
    33989394450872125, 6714245517766967, 6442943495848765, 35833074500151989, 9192292814470767, 31989813499532049,
    11194141238863136, 11194141238863136, 10711666973659367, 6442943495848765, 54941474575513061, 54941474392136489,
    30930439301435900, 7451211111832378, 7179909090014935, 32773862227482370, 9929258415949272, 28930858367860654,
    11931106840579056, 11931106840579056, 11448632567730597, 7179909090014935, 32824759730664159, 32824760069366870,
    20989592013168019, 11194141238863136, 16052122233990708, 15875965281657251, 11931106840579056, 11194141238863136,
    11931106840579056, 16866566583203111, 11931106840579056, 11194141238863136, 20868333509456728, 16903799491708359,
    16052122233990708, 16866566583203111, 11931106840579056, 16903799491708359, 11931106840579056, 16866566583203111,
    11931106840579056, 11194141238863136, 30445069027528702, 33766268899553436, 34766268546984657, 30445069027528702,
    11194141238863136, 16052122233990708, 15875965281657251, 11931106840579056, 11194141238863136, 11931106840579056,
    16866566583203111, 11931106840579056, 11194141238863136, 20868333509456728
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
noncomputable def negativeCeiling : ℝ := 6996451309 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 105592114556965266978242560, coefficient := (-105592114556965266978242560) }, { argument := 5477945120128788447887360, coefficient := (-5477945120128788447887360) }, { argument := 3461709384326270049811693568, coefficient := (-3461709384326270049811693568) }, { argument := 138398498903585405400141266944, coefficient := (-138398498903585405400141266944) }, { argument := 138398465081480146253678379008, coefficient := (-138398465081480146253678379008) }, { argument := 3461709384326270049811693568, coefficient := (-3461709384326270049811693568) }, { argument := 314591497449300842285455376384, coefficient := (-314591497449300842285455376384) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 105176546306472738199437312, coefficient := (-105176546306472738199437312) }, { argument := 1129145696188288726154805772288, coefficient := (-1129145696188288726154805772288) }, { argument := 2828886417898232268812451840, coefficient := (-2828886417898232268812451840) }, { argument := 314682887692296619674287734784, coefficient := (-314682887692296619674287734784) }, { argument := 2832513195357076156336570368, coefficient := (-2832513195357076156336570368) }, { argument := 2832513195357076156336570368, coefficient := (-2832513195357076156336570368) }, { argument := 2027368599493733125982257152, coefficient := (-2027368599493733125982257152) }, { argument := 105176546306472738199437312, coefficient := (-105176546306472738199437312) }, { argument := 9738041979305314945636900012032, coefficient := (-9738041979305314945636900012032) }, { argument := 9738040741532727686449982341120, coefficient := (-9738040741532727686449982341120) }, { argument := 18874685911288006808726142976, coefficient := (-18874685911288006808726142976) }, { argument := 105781009216280052786790400, coefficient := (-105781009216280052786790400) }, { argument := 5477945120128788447887360, coefficient := (-5477945120128788447887360) }, { argument := 67733782825436867051537825792, coefficient := (-67733782825436867051537825792) }, { argument := 147337834265532930667315200, coefficient := (-147337834265532930667315200) }, { argument := 18880169325867753452056084480, coefficient := (-18880169325867753452056084480) }, { argument := 147526728924847716475863040, coefficient := (-147526728924847716475863040) }, { argument := 147526728924847716475863040, coefficient := (-147526728924847716475863040) }, { argument := 105592114556965266978242560, coefficient := (-105592114556965266978242560) }, { argument := 5477945120128788447887360, coefficient := (-5477945120128788447887360) }, { argument := 70166046333961848388631658496, coefficient := (-70166046333961848388631658496) }, { argument := 70166062806904306211261251584, coefficient := (-70166062806904306211261251584) }, { argument := 9832330639553782297596526592, coefficient := (-9832330639553782297596526592) }, { argument := 177032074709817259771035648, coefficient := (-177032074709817259771035648) }, { argument := 2566965083292350266680016896, coefficient := (-2566965083292350266680016896) }, { argument := 4543823250885309667456581632, coefficient := (-4543823250885309667456581632) }, { argument := 147526728924847716475863040, coefficient := (-147526728924847716475863040) }, { argument := 2832513195357076156336570368, coefficient := (-2832513195357076156336570368) }, { argument := 147526728924847716475863040, coefficient := (-147526728924847716475863040) }, { argument := 4514317905100340124161409024, coefficient := (-4514317905100340124161409024) }, { argument := 4720855325595126927227617280, coefficient := (-4720855325595126927227617280) }, { argument := 2832513195357076156336570368, coefficient := (-2832513195357076156336570368) }, { argument := 72317602518960350616468062208, coefficient := (-72317602518960350616468062208) }, { argument := 4632339288240218297342099456, coefficient := (-4632339288240218297342099456) }, { argument := 2566965083292350266680016896, coefficient := (-2566965083292350266680016896) }, { argument := 4514317905100340124161409024, coefficient := (-4514317905100340124161409024) }, { argument := 147526728924847716475863040, coefficient := (-147526728924847716475863040) }, { argument := 4632339288240218297342099456, coefficient := (-4632339288240218297342099456) }, { argument := 147526728924847716475863040, coefficient := (-147526728924847716475863040) }, { argument := 4514317905100340124161409024, coefficient := (-4514317905100340124161409024) }, { argument := 4720855325595126927227617280, coefficient := (-4720855325595126927227617280) }, { argument := 177032074709817259771035648, coefficient := (-177032074709817259771035648) }, { argument := 3370611768949262943237701632, coefficient := (-3370611768949262943237701632) }, { argument := 134756433142964736836979654656, coefficient := (-134756433142964736836979654656) }, { argument := 134756400210914879247002632192, coefficient := (-134756400210914879247002632192) }, { argument := 3370611768949262943237701632, coefficient := (-3370611768949262943237701632) }, { argument := 177032074709817259771035648, coefficient := (-177032074709817259771035648) }, { argument := 2566965083292350266680016896, coefficient := (-2566965083292350266680016896) }, { argument := 4543823250885309667456581632, coefficient := (-4543823250885309667456581632) }, { argument := 147526728924847716475863040, coefficient := (-147526728924847716475863040) }, { argument := 2832513195357076156336570368, coefficient := (-2832513195357076156336570368) }, { argument := 147526728924847716475863040, coefficient := (-147526728924847716475863040) }, { argument := 4514317905100340124161409024, coefficient := (-4514317905100340124161409024) }, { argument := 4720855325595126927227617280, coefficient := (-4720855325595126927227617280) }, { argument := 2832513195357076156336570368, coefficient := (-2832513195357076156336570368) }, { argument := 72317602518960350616468062208, coefficient := (-72317602518960350616468062208) }] }

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
def constantNumerator : ℤ := (-1271269850634087136561425798922240)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    122617, 67947, 119493, 3905, 122617, 3905,
    119493, 3905, 2343, 27615597807, 276016619139, 552033103371,
    27615597807, 53890915415, 5355, 4437, 193429927165, 29835,
    13476642731, 119493, 119493, 85527, 4437, 1461769841,
    14610321757, 29220636373, 1461769841, 107101495093, 175, 145,
    384445383431, 975, 26783151985, 3905, 3905, 2795,
    145, 19620951809, 19620956415, 1677, 48633, 43043,
    2795, 1677, 2795, 85527, 2795, 1677,
    1370109, 87763, 48633, 85527, 2795, 87763,
    2795, 85527, 2795, 1677, 16948628697, 169400757669,
    338801432541, 16948628697, 17054039249, 105
  ]
def negativeCoefficients : Array ℕ := #[
    4632339288240218297342099456, 2566965083292350266680016896, 4514317905100340124161409024, 147526728924847716475863040, 4632339288240218297342099456, 147526728924847716475863040,
    4514317905100340124161409024, 4720855325595126927227617280, 177032074709817259771035648, 127354466297055934990440726528, 5091607933347694651299933978624, 5091606689050243275332694048768,
    127354466297055934990440726528, 497055962279216985707716280320, 3236898882018169615275786240, 167625120675940926505353216, 1784076181304516980223844024320, 4508537728525307678419845120,
    497200358863150313982071406592, 4514317905100340124161409024, 4514317905100340124161409024, 3231118705443137169534222336, 167625120675940926505353216, 3370611768949262943237701632,
    134756433142964736836979654656, 134756400210914879247002632192, 3370611768949262943237701632, 493918467473057593177063555072, 3384992294920961689177292800, 175294243844121230332395520,
    1772941399617698874385051418624, 4714810696497053781354086400, 494061950154560963677530357760, 4720855325595126927227617280, 4720855325595126927227617280, 3378947665822888543303761920,
    175294243844121230332395520, 90485669125802864030133518336, 90485690367228664906682204160, 126710537468358320373891072, 1837302793291195645421420544, 3252237128354530222929870848,
    105592114556965266978242560, 2027368599493733125982257152, 105592114556965266978242560, 3231118705443137169534222336, 3378947665822888543303761920, 2027368599493733125982257152,
    51761254555824373872734502912, 3315592397088709383116816384, 1837302793291195645421420544, 3231118705443137169534222336, 105592114556965266978242560, 3315592397088709383116816384,
    105592114556965266978242560, 3231118705443137169534222336, 3378947665822888543303761920, 126710537468358320373891072, 39080876996736048720242540544, 1562446211306266813596331671552,
    1562445829472499545863895384064, 39080876996736048720242540544, 314591497449300842285455376384, 2030995376952577013506375680
  ]
def negativeScales : Array ℕ := #[
    16, 16, 16, 11, 16, 11,
    16, 11, 11, 34, 38, 39,
    34, 35, 12, 12, 37, 14,
    33, 16, 16, 16, 12, 30,
    33, 34, 30, 36, 7, 7,
    38, 9, 34, 11, 11, 11,
    7, 34, 34, 10, 15, 15,
    11, 10, 11, 16, 11, 10,
    20, 16, 15, 16, 11, 16,
    11, 16, 11, 10, 33, 37,
    38, 33, 33, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16903799491708359, 16052122233990708, 16866566583203111, 11931106840579056, 16903799491708359, 11931106840579056,
    16866566583203111, 11931106840579056, 11194141238863136, 34684764307325522, 38005964178980333, 39005963826411556,
    34684764307325522, 35649323042088436, 12386670859637623, 12115368837820224, 37493020067284943, 14864718158730226,
    33649742089436104, 16866566583203111, 16866566583203111, 16384092315535846, 12115368837820224, 30445069027528702,
    33766268899553436, 34766268546984657, 30445069027528702, 36640187663438097, 7451211111832378, 7179909090014935,
    38483987698775227, 9929258415949272, 34640606703635472, 11931106840579056, 11931106840579056, 11448632567730597,
    7179909090014935, 34191675977016786, 34191676315688051, 10711666973659367, 15569647968694305, 15393491013538097,
    11448632567730597, 10711666973659367, 11448632567730597, 16384092315535846, 11448632567730597, 10711666973659367,
    20385859241710034, 16421325221734833, 15569647968694305, 16384092315535846, 11448632567730597, 16421325221734833,
    11448632567730597, 16384092315535846, 11448632567730597, 10711666973659367, 33980449516674841, 37301649371104442,
    38301649018535665, 33980449516674841, 33989394450872125, 6714245517766967
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
noncomputable def negativeCeiling : ℝ := 454616283 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4632339288240218297342099456, coefficient := (-4632339288240218297342099456) }, { argument := 2566965083292350266680016896, coefficient := (-2566965083292350266680016896) }, { argument := 4514317905100340124161409024, coefficient := (-4514317905100340124161409024) }, { argument := 147526728924847716475863040, coefficient := (-147526728924847716475863040) }, { argument := 4632339288240218297342099456, coefficient := (-4632339288240218297342099456) }, { argument := 147526728924847716475863040, coefficient := (-147526728924847716475863040) }, { argument := 4514317905100340124161409024, coefficient := (-4514317905100340124161409024) }, { argument := 4720855325595126927227617280, coefficient := (-4720855325595126927227617280) }, { argument := 177032074709817259771035648, coefficient := (-177032074709817259771035648) }, { argument := 127354466297055934990440726528, coefficient := (-127354466297055934990440726528) }, { argument := 5091607933347694651299933978624, coefficient := (-5091607933347694651299933978624) }, { argument := 5091606689050243275332694048768, coefficient := (-5091606689050243275332694048768) }, { argument := 127354466297055934990440726528, coefficient := (-127354466297055934990440726528) }, { argument := 497055962279216985707716280320, coefficient := (-497055962279216985707716280320) }, { argument := 3236898882018169615275786240, coefficient := (-3236898882018169615275786240) }, { argument := 167625120675940926505353216, coefficient := (-167625120675940926505353216) }, { argument := 1784076181304516980223844024320, coefficient := (-1784076181304516980223844024320) }, { argument := 4508537728525307678419845120, coefficient := (-4508537728525307678419845120) }, { argument := 497200358863150313982071406592, coefficient := (-497200358863150313982071406592) }, { argument := 4514317905100340124161409024, coefficient := (-4514317905100340124161409024) }, { argument := 4514317905100340124161409024, coefficient := (-4514317905100340124161409024) }, { argument := 3231118705443137169534222336, coefficient := (-3231118705443137169534222336) }, { argument := 167625120675940926505353216, coefficient := (-167625120675940926505353216) }, { argument := 3370611768949262943237701632, coefficient := (-3370611768949262943237701632) }, { argument := 134756433142964736836979654656, coefficient := (-134756433142964736836979654656) }, { argument := 134756400210914879247002632192, coefficient := (-134756400210914879247002632192) }, { argument := 3370611768949262943237701632, coefficient := (-3370611768949262943237701632) }, { argument := 493918467473057593177063555072, coefficient := (-493918467473057593177063555072) }, { argument := 3384992294920961689177292800, coefficient := (-3384992294920961689177292800) }, { argument := 175294243844121230332395520, coefficient := (-175294243844121230332395520) }, { argument := 1772941399617698874385051418624, coefficient := (-1772941399617698874385051418624) }, { argument := 4714810696497053781354086400, coefficient := (-4714810696497053781354086400) }, { argument := 494061950154560963677530357760, coefficient := (-494061950154560963677530357760) }, { argument := 4720855325595126927227617280, coefficient := (-4720855325595126927227617280) }, { argument := 4720855325595126927227617280, coefficient := (-4720855325595126927227617280) }, { argument := 3378947665822888543303761920, coefficient := (-3378947665822888543303761920) }, { argument := 175294243844121230332395520, coefficient := (-175294243844121230332395520) }, { argument := 90485669125802864030133518336, coefficient := (-90485669125802864030133518336) }, { argument := 90485690367228664906682204160, coefficient := (-90485690367228664906682204160) }, { argument := 126710537468358320373891072, coefficient := (-126710537468358320373891072) }, { argument := 1837302793291195645421420544, coefficient := (-1837302793291195645421420544) }, { argument := 3252237128354530222929870848, coefficient := (-3252237128354530222929870848) }, { argument := 105592114556965266978242560, coefficient := (-105592114556965266978242560) }, { argument := 2027368599493733125982257152, coefficient := (-2027368599493733125982257152) }, { argument := 105592114556965266978242560, coefficient := (-105592114556965266978242560) }, { argument := 3231118705443137169534222336, coefficient := (-3231118705443137169534222336) }, { argument := 3378947665822888543303761920, coefficient := (-3378947665822888543303761920) }, { argument := 2027368599493733125982257152, coefficient := (-2027368599493733125982257152) }, { argument := 51761254555824373872734502912, coefficient := (-51761254555824373872734502912) }, { argument := 3315592397088709383116816384, coefficient := (-3315592397088709383116816384) }, { argument := 1837302793291195645421420544, coefficient := (-1837302793291195645421420544) }, { argument := 3231118705443137169534222336, coefficient := (-3231118705443137169534222336) }, { argument := 105592114556965266978242560, coefficient := (-105592114556965266978242560) }, { argument := 3315592397088709383116816384, coefficient := (-3315592397088709383116816384) }, { argument := 105592114556965266978242560, coefficient := (-105592114556965266978242560) }, { argument := 3231118705443137169534222336, coefficient := (-3231118705443137169534222336) }, { argument := 3378947665822888543303761920, coefficient := (-3378947665822888543303761920) }, { argument := 126710537468358320373891072, coefficient := (-126710537468358320373891072) }, { argument := 39080876996736048720242540544, coefficient := (-39080876996736048720242540544) }, { argument := 1562446211306266813596331671552, coefficient := (-1562446211306266813596331671552) }, { argument := 1562445829472499545863895384064, coefficient := (-1562445829472499545863895384064) }, { argument := 39080876996736048720242540544, coefficient := (-39080876996736048720242540544) }, { argument := 314591497449300842285455376384, coefficient := (-314591497449300842285455376384) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15
