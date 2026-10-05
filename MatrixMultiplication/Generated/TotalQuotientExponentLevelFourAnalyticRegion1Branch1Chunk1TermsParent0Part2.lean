import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 1, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1032017437087394027394609142824960)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2475668955, 50975940885, 2475668955, 60426111, 4770556805, 47681493985,
    95362964665, 4770556805, 274280283, 1998274851, 548560935, 17524247909,
    175154044993, 350308004377, 17524247909, 224086991211, 1632590553267, 448174283895,
    1929, 1929, 14354001477, 104576383869, 28708022265, 3489,
    3489, 755141989, 107468025, 3834207383, 1212853425, 107468025,
    7668412937, 107468025, 107468025, 4455317265, 27634635, 1212853425,
    4455317265, 755141989, 107468025, 27634635, 107468025, 8191318047,
    2475668955, 64238915, 68603747659, 3987754185, 16402412615, 3987754185,
    4155763655, 2475668955, 123536375, 4521852645, 4465390875, 4521852645,
    4465390875, 13988294433, 101912017401, 27976607685, 1929, 1929,
    57, 57, 3015275, 123536375
  ]
def negativeCoefficients : Array ℕ := #[
    22834015812056484311350640640, 235085033855535546459268055040, 22834015812056484311350640640, 139333125623320693463580672, 22000310117732130763801886720, 879568316593416382015351029760,
    879568101642731063114800824320, 22000310117732130763801886720, 40476625479725029416316698624, 147446659061308349090956836864, 40476652707119282211614883840, 80816329065390687945003892736,
    3231021841460878912162719858688, 3231021051857222209062217711616, 80816329065390687945003892736, 1033418844279229657285335711744, 3764497514159028787728491741184, 1033419539428639173965292503040,
    18656143248292957424065708032, 18656143248292957424065708032, 66196147919966975191267934208, 241136723673181362575835660288, 66196192448101326116911841280, 33743537477083529524398784512,
    33743537477083529524398784512, 3482477752598748353901101056, 1982435153282019935807078400, 70728642319728659003686780928, 22373196729897082132679884800, 1982435153282019935807078400,
    70728625450181203596301828096, 1982435153282019935807078400, 1982435153282019935807078400, 82186097354634597910173450240, 2039076157661506219687280640, 22373196729897082132679884800,
    82186097354634597910173450240, 3482477752598748353901101056, 1982435153282019935807078400, 2039076157661506219687280640, 1982435153282019935807078400, 37775786909841837097104703488,
    22834015812056484311350640640, 1184998824577781620948336640, 158189471945365471890262458368, 36780540439779606465588756480, 37821388462536254909034004480, 36780540439779606465588756480,
    38330154287304397816059658240, 22834015812056484311350640640, 1139421946709405404758016000, 10426682310167701367071703040, 10296490332525369898303488000, 10426682310167701367071703040,
    10296490332525369898303488000, 64509621858311765632254738432, 234993112878960181363712458752, 64509665251971356024761221120, 18656143248292957424065708032, 18656143248292957424065708032,
    1102540347488541807332032512, 1102540347488541807332032512, 6952750779606821031116800, 1139421946709405404758016000
  ]
def negativeScales : Array ℕ := #[
    31, 35, 31, 25, 32, 35,
    36, 32, 28, 30, 29, 34,
    37, 38, 34, 37, 40, 38,
    10, 10, 33, 36, 34, 11,
    11, 29, 26, 31, 30, 26,
    32, 26, 26, 32, 24, 30,
    32, 29, 26, 24, 26, 32,
    31, 25, 35, 31, 33, 31,
    31, 31, 26, 32, 32, 32,
    32, 33, 36, 34, 10, 10,
    5, 5, 21, 26
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31205171265101290, 35569097447810268, 31205171265101290, 25848668759657764, 32151510517057940, 35472710388763228,
    36472710036194451, 32151510517057940, 28031075674976223, 30896107889088806, 29031076645432949, 34028633478060219,
    37349833349765402, 38349832997196625, 34028633478060219, 37705267943203804, 40570300153164361, 38705268913660532,
    10913637433615165, 10913637433615165, 33740733923330102, 36605766133193344, 34740734893786832, 11768597882530236,
    11768597882530236, 29492172698326660, 26679332237229289, 31836281226316625, 30175758063304617, 26679332237229289,
    32836280882218178, 26679332237229289, 26679332237229289, 32052881024306896, 24719974221797463, 30175758063304617,
    32052881024306896, 29492172698326660, 26679332237229289, 24719974221797463, 26679332237229289, 32931448473016643,
    31205171265101290, 25936944198394613, 35997568361186070, 31892929339029355, 33933188991768299, 31892929339029355,
    31952466473027938, 31205171265101290, 26880360664739007, 32074266833295617, 32056139320204539, 32074266833295617,
    32056139320204539, 33703501017026303, 36568533226990051, 34703501987483031, 10913637433615165, 10913637433615165,
    5832890015409720, 5832890015409720, 21523858154549244, 26880360664739007
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
noncomputable def negativeCeiling : ℝ := 1486752981 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 22834015812056484311350640640, coefficient := (-22834015812056484311350640640) }, { argument := 235085033855535546459268055040, coefficient := (-235085033855535546459268055040) }, { argument := 22834015812056484311350640640, coefficient := (-22834015812056484311350640640) }, { argument := 139333125623320693463580672, coefficient := (-139333125623320693463580672) }, { argument := 22000310117732130763801886720, coefficient := (-22000310117732130763801886720) }, { argument := 879568316593416382015351029760, coefficient := (-879568316593416382015351029760) }, { argument := 879568101642731063114800824320, coefficient := (-879568101642731063114800824320) }, { argument := 22000310117732130763801886720, coefficient := (-22000310117732130763801886720) }, { argument := 40476625479725029416316698624, coefficient := (-40476625479725029416316698624) }, { argument := 147446659061308349090956836864, coefficient := (-147446659061308349090956836864) }, { argument := 40476652707119282211614883840, coefficient := (-40476652707119282211614883840) }, { argument := 80816329065390687945003892736, coefficient := (-80816329065390687945003892736) }, { argument := 3231021841460878912162719858688, coefficient := (-3231021841460878912162719858688) }, { argument := 3231021051857222209062217711616, coefficient := (-3231021051857222209062217711616) }, { argument := 80816329065390687945003892736, coefficient := (-80816329065390687945003892736) }, { argument := 1033418844279229657285335711744, coefficient := (-1033418844279229657285335711744) }, { argument := 3764497514159028787728491741184, coefficient := (-3764497514159028787728491741184) }, { argument := 1033419539428639173965292503040, coefficient := (-1033419539428639173965292503040) }, { argument := 18656143248292957424065708032, coefficient := (-18656143248292957424065708032) }, { argument := 18656143248292957424065708032, coefficient := (-18656143248292957424065708032) }, { argument := 66196147919966975191267934208, coefficient := (-66196147919966975191267934208) }, { argument := 241136723673181362575835660288, coefficient := (-241136723673181362575835660288) }, { argument := 66196192448101326116911841280, coefficient := (-66196192448101326116911841280) }, { argument := 33743537477083529524398784512, coefficient := (-33743537477083529524398784512) }, { argument := 33743537477083529524398784512, coefficient := (-33743537477083529524398784512) }, { argument := 3482477752598748353901101056, coefficient := (-3482477752598748353901101056) }, { argument := 1982435153282019935807078400, coefficient := (-1982435153282019935807078400) }, { argument := 70728642319728659003686780928, coefficient := (-70728642319728659003686780928) }, { argument := 22373196729897082132679884800, coefficient := (-22373196729897082132679884800) }, { argument := 1982435153282019935807078400, coefficient := (-1982435153282019935807078400) }, { argument := 70728625450181203596301828096, coefficient := (-70728625450181203596301828096) }, { argument := 1982435153282019935807078400, coefficient := (-1982435153282019935807078400) }, { argument := 1982435153282019935807078400, coefficient := (-1982435153282019935807078400) }, { argument := 82186097354634597910173450240, coefficient := (-82186097354634597910173450240) }, { argument := 2039076157661506219687280640, coefficient := (-2039076157661506219687280640) }, { argument := 22373196729897082132679884800, coefficient := (-22373196729897082132679884800) }, { argument := 82186097354634597910173450240, coefficient := (-82186097354634597910173450240) }, { argument := 3482477752598748353901101056, coefficient := (-3482477752598748353901101056) }, { argument := 1982435153282019935807078400, coefficient := (-1982435153282019935807078400) }, { argument := 2039076157661506219687280640, coefficient := (-2039076157661506219687280640) }, { argument := 1982435153282019935807078400, coefficient := (-1982435153282019935807078400) }, { argument := 37775786909841837097104703488, coefficient := (-37775786909841837097104703488) }, { argument := 22834015812056484311350640640, coefficient := (-22834015812056484311350640640) }, { argument := 1184998824577781620948336640, coefficient := (-1184998824577781620948336640) }, { argument := 158189471945365471890262458368, coefficient := (-158189471945365471890262458368) }, { argument := 36780540439779606465588756480, coefficient := (-36780540439779606465588756480) }, { argument := 37821388462536254909034004480, coefficient := (-37821388462536254909034004480) }, { argument := 36780540439779606465588756480, coefficient := (-36780540439779606465588756480) }, { argument := 38330154287304397816059658240, coefficient := (-38330154287304397816059658240) }, { argument := 22834015812056484311350640640, coefficient := (-22834015812056484311350640640) }, { argument := 1139421946709405404758016000, coefficient := (-1139421946709405404758016000) }, { argument := 10426682310167701367071703040, coefficient := (-10426682310167701367071703040) }, { argument := 10296490332525369898303488000, coefficient := (-10296490332525369898303488000) }, { argument := 10426682310167701367071703040, coefficient := (-10426682310167701367071703040) }, { argument := 10296490332525369898303488000, coefficient := (-10296490332525369898303488000) }, { argument := 64509621858311765632254738432, coefficient := (-64509621858311765632254738432) }, { argument := 234993112878960181363712458752, coefficient := (-234993112878960181363712458752) }, { argument := 64509665251971356024761221120, coefficient := (-64509665251971356024761221120) }, { argument := 18656143248292957424065708032, coefficient := (-18656143248292957424065708032) }, { argument := 18656143248292957424065708032, coefficient := (-18656143248292957424065708032) }, { argument := 1102540347488541807332032512, coefficient := (-1102540347488541807332032512) }, { argument := 1102540347488541807332032512, coefficient := (-1102540347488541807332032512) }, { argument := 6952750779606821031116800, coefficient := (-6952750779606821031116800) }, { argument := 1139421946709405404758016000, coefficient := (-1139421946709405404758016000) }] }

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


end Parent0

namespace Parent0

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 6149231586102308877507623424884736
def positiveArguments : Array ℕ := #[
    99, 489, 535, 489, 535, 87,
    14529
  ]
def positiveCoefficients : Array ℕ := #[
    62748704711297355374086808666112, 37834542450659434651604484096, 41393620063604902941939466240, 37834542450659434651604484096, 41393620063604902941939466240, 26925195854457020979055951872,
    562063463461790312937792995328
  ]
def positiveScales : Array ℕ := #[
    6, 8, 9, 8, 9, 6,
    13
  ]
def negativeArguments : Array ℕ := #[
    2543709625, 123536375, 3015275, 422707565, 4224942505, 8449882945,
    422707565, 457133805, 3330458085, 914268225, 108696231, 1086413787,
    2172827043, 108696231, 14354001477, 104576383869, 28708022265, 57,
    57, 457133805, 3330458085, 914268225, 111, 111,
    422707565, 4224942505, 8449882945, 422707565, 13988294433, 101912017401,
    27976607685, 111, 111, 457133805, 3330458085, 914268225,
    3489, 3489, 111, 111, 275003949, 60426111,
    1567943, 4061559031, 97333077, 1100137145, 97333077, 101433851,
    60426111, 3015275, 611975451, 22514405, 611975451, 22514405,
    9, 9, 1
  ]
def negativeCoefficients : Array ℕ := #[
    11730790112551673975013376000, 1139421946709405404758016000, 6952750779606821031116800, 1949394567393986270210293760, 77936433115872337646929838080, 77936414069609081541817794560,
    1949394567393986270210293760, 2108157577069011948766494720, 7679513492776476515154001920, 2108158995162462615188275200, 2005091555033814449359159296, 80163188347754404436842119168,
    80163168757312198157298302976, 2005091555033814449359159296, 66196147919966975191267934208, 241136723673181362575835660288, 66196192448101326116911841280, 1102540347488541807332032512,
    1102540347488541807332032512, 2108157577069011948766494720, 7679513492776476515154001920, 2108158995162462615188275200, 1073526127817790707139084288, 1073526127817790707139084288,
    1949394567393986270210293760, 77936433115872337646929838080, 77936414069609081541817794560, 1949394567393986270210293760, 64509621858311765632254738432, 234993112878960181363712458752,
    64509665251971356024761221120, 1073526127817790707139084288, 1073526127817790707139084288, 67461042466208382360527831040, 245744431768847248484928061440, 67461087845198803686024806400,
    33743537477083529524398784512, 33743537477083529524398784512, 1073526127817790707139084288, 1073526127817790707139084288, 2536463733231236886709665792, 139333125623320693463580672,
    7230860810791093872361472, 9365317498140094879615680512, 224434795165708182884450304, 2536743544974561959257047040, 224434795165708182884450304, 233890536225973459486769152,
    139333125623320693463580672, 6952750779606821031116800, 1411119315498747511651172352, 51914683375855837181378560, 1411119315498747511651172352, 51914683375855837181378560,
    1392682544196052809261514752, 1392682544196052809261514752, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    31, 26, 21, 28, 31, 32,
    28, 28, 31, 29, 26, 30,
    31, 26, 33, 36, 34, 5,
    5, 28, 31, 29, 6, 6,
    28, 31, 32, 28, 33, 36,
    34, 6, 6, 28, 31, 29,
    11, 11, 6, 6, 28, 25,
    20, 31, 26, 30, 26, 26,
    25, 21, 29, 24, 29, 24,
    3, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6629356620078832, 8933690654464738, 9063395081288509, 8933690654464738, 9063395081288509, 6442943495848725,
    13826647788254566
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    31244286844387436, 26880360664739007, 21523858154549244, 28655084690962677, 31976284578782611, 32976284226213741,
    28655084690962677, 28768041269474333, 31633073479196219, 29768042239931066, 26695726675501230, 30016926547140969,
    31016926194572192, 26695726675501230, 33740733923330102, 36605766133193344, 34740734893786832, 5832890015409720,
    5832890015409720, 28768041269474333, 31633073479196219, 29768042239931066, 6794415866926375, 6794415866926375,
    28655084690962677, 31976284578782611, 32976284226213741, 28655084690962677, 33703501017026303, 36568533226990051,
    34703501987483031, 6794415866926375, 6794415866926375, 28768041269474333, 31633073479196219, 29768042239931066,
    11768597882530236, 11768597882530236, 6794415866926375, 6794415866926375, 28034877094688236, 25848668759657764,
    20580441682918281, 31919386472913488, 26536426828052586, 30035036237807273, 26536426828052586, 26595963955034128,
    25848668759657764, 21523858154549244, 29188898540397695, 24424345015535906, 29188898540397695, 24424345015535906,
    3169925001442313, 3169925001442313, 0
  ]

abbrev PositiveTerm := Fin 7
abbrev NegativeTerm := Fin 57
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
noncomputable def positiveFloor : ℝ := 5120022281 / 1000000000000
noncomputable def negativeCeiling : ℝ := 336935171 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 11730790112551673975013376000, coefficient := (-11730790112551673975013376000) }, { argument := 1139421946709405404758016000, coefficient := (-1139421946709405404758016000) }, { argument := 6952750779606821031116800, coefficient := (-6952750779606821031116800) }, { argument := 1949394567393986270210293760, coefficient := (-1949394567393986270210293760) }, { argument := 77936433115872337646929838080, coefficient := (-77936433115872337646929838080) }, { argument := 77936414069609081541817794560, coefficient := (-77936414069609081541817794560) }, { argument := 1949394567393986270210293760, coefficient := (-1949394567393986270210293760) }, { argument := 2108157577069011948766494720, coefficient := (-2108157577069011948766494720) }, { argument := 7679513492776476515154001920, coefficient := (-7679513492776476515154001920) }, { argument := 2108158995162462615188275200, coefficient := (-2108158995162462615188275200) }, { argument := 2005091555033814449359159296, coefficient := (-2005091555033814449359159296) }, { argument := 80163188347754404436842119168, coefficient := (-80163188347754404436842119168) }, { argument := 80163168757312198157298302976, coefficient := (-80163168757312198157298302976) }, { argument := 2005091555033814449359159296, coefficient := (-2005091555033814449359159296) }, { argument := 66196147919966975191267934208, coefficient := (-66196147919966975191267934208) }, { argument := 241136723673181362575835660288, coefficient := (-241136723673181362575835660288) }, { argument := 66196192448101326116911841280, coefficient := (-66196192448101326116911841280) }, { argument := 1102540347488541807332032512, coefficient := (-1102540347488541807332032512) }, { argument := 1102540347488541807332032512, coefficient := (-1102540347488541807332032512) }, { argument := 2108157577069011948766494720, coefficient := (-2108157577069011948766494720) }, { argument := 7679513492776476515154001920, coefficient := (-7679513492776476515154001920) }, { argument := 2108158995162462615188275200, coefficient := (-2108158995162462615188275200) }, { argument := 1073526127817790707139084288, coefficient := (-1073526127817790707139084288) }, { argument := 1073526127817790707139084288, coefficient := (-1073526127817790707139084288) }, { argument := 1949394567393986270210293760, coefficient := (-1949394567393986270210293760) }, { argument := 77936433115872337646929838080, coefficient := (-77936433115872337646929838080) }, { argument := 77936414069609081541817794560, coefficient := (-77936414069609081541817794560) }, { argument := 1949394567393986270210293760, coefficient := (-1949394567393986270210293760) }, { argument := 64509621858311765632254738432, coefficient := (-64509621858311765632254738432) }, { argument := 234993112878960181363712458752, coefficient := (-234993112878960181363712458752) }, { argument := 64509665251971356024761221120, coefficient := (-64509665251971356024761221120) }, { argument := 1073526127817790707139084288, coefficient := (-1073526127817790707139084288) }, { argument := 1073526127817790707139084288, coefficient := (-1073526127817790707139084288) }, { argument := 67461042466208382360527831040, coefficient := (-67461042466208382360527831040) }, { argument := 245744431768847248484928061440, coefficient := (-245744431768847248484928061440) }, { argument := 67461087845198803686024806400, coefficient := (-67461087845198803686024806400) }, { argument := 33743537477083529524398784512, coefficient := (-33743537477083529524398784512) }, { argument := 33743537477083529524398784512, coefficient := (-33743537477083529524398784512) }, { argument := 1073526127817790707139084288, coefficient := (-1073526127817790707139084288) }, { argument := 1073526127817790707139084288, coefficient := (-1073526127817790707139084288) }, { argument := 2536463733231236886709665792, coefficient := (-2536463733231236886709665792) }, { argument := 139333125623320693463580672, coefficient := (-139333125623320693463580672) }, { argument := 7230860810791093872361472, coefficient := (-7230860810791093872361472) }, { argument := 9365317498140094879615680512, coefficient := (-9365317498140094879615680512) }, { argument := 224434795165708182884450304, coefficient := (-224434795165708182884450304) }, { argument := 2536743544974561959257047040, coefficient := (-2536743544974561959257047040) }, { argument := 224434795165708182884450304, coefficient := (-224434795165708182884450304) }, { argument := 233890536225973459486769152, coefficient := (-233890536225973459486769152) }, { argument := 139333125623320693463580672, coefficient := (-139333125623320693463580672) }, { argument := 6952750779606821031116800, coefficient := (-6952750779606821031116800) }, { argument := 1411119315498747511651172352, coefficient := (-1411119315498747511651172352) }, { argument := 51914683375855837181378560, coefficient := (-51914683375855837181378560) }, { argument := 1411119315498747511651172352, coefficient := (-1411119315498747511651172352) }, { argument := 51914683375855837181378560, coefficient := (-51914683375855837181378560) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 1392682544196052809261514752, coefficient := (-1392682544196052809261514752) }, { argument := 62748704711297355374086808666112, coefficient := 62748704711297355374086808666112 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 26925195854457020979055951872, coefficient := 26925195854457020979055951872 }, { argument := 562063463461790312937792995328, coefficient := 562063463461790312937792995328 }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1
