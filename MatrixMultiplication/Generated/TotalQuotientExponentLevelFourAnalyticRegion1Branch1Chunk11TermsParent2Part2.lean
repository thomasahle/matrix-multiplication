import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
parent chunk 11, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-233282999999621928918482136596480)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    61191357597693, 155393, 2345987954746647, 49175, 5901, 155393,
    308819, 49175, 4766041, 304885, 244765672857237, 155393,
    5901, 304885, 5901, 155393, 155393, 123960449763,
    38926775, 7720535625, 7720535625, 38926775, 6799107, 2309815305,
    346731, 23497117665, 109725, 13167, 346731, 689073,
    109725, 10634547, 680295, 1154910981, 346731, 13167,
    680295, 13167, 346731, 346731, 6799107, 1072046195,
    20959785545, 41919567235, 134005935, 651, 1995, 5901,
    13167, 651, 6573, 13377, 651, 1995,
    651, 33635, 103075, 304885, 680295, 33635,
    339605, 691145, 33635, 103075
  ]
def negativeCoefficients : Array ℕ := #[
    275581375275264964085025865728, 2935290779490251114767450112, 2641347619703167865495620681728, 1857778974360918427068006400, 111466738461655105624080384, 2935290779490251114767450112,
    2916712989746641930496770048, 1857778974360918427068006400, 45013984548765053487857795072, 2879557410259423561955409920, 275581648268235320045378469888, 2935290779490251114767450112,
    111466738461655105624080384, 2879557410259423561955409920, 111466738461655105624080384, 2935290779490251114767450112, 2935290779490251114767450112, 2233072941445303556785569792,
    89759032004984391388364800, 17802343098291527394263040000, 17802343098291527394263040000, 89759032004984391388364800, 250842773517534256718413824, 42608571788872370447324282880,
    3274781705943749909180055552, 433445316036094767355542896640, 2072646649331487284291174400, 124358798959889237057470464, 3274781705943749909180055552, 3254055239450435036337143808,
    2072646649331487284291174400, 50220228313301936898375155712, 3212602306463805290651320320, 42608694588847669131809390592, 3274781705943749909180055552, 124358798959889237057470464,
    3212602306463805290651320320, 124358798959889237057470464, 3274781705943749909180055552, 3274781705943749909180055552, 250842773517534256718413824, 4943940448589781086272225280,
    193319899894225937244734095360, 193319882116176336207153725440, 4943946374606314765465681920, 6148521160696278068232192, 150737938133199075221176320, 111466738461655105624080384,
    124358798959889237057470464, 6148521160696278068232192, 124160459567608711958495232, 126342192882694488047222784, 6148521160696278068232192, 150737938133199075221176320,
    6148521160696278068232192, 158836796651320516762664960, 3894063401774309443213721600, 2879557410259423561955409920, 3212602306463805290651320320, 158836796651320516762664960,
    3207478538829891725594460160, 3263839982802940941219921920, 158836796651320516762664960, 3894063401774309443213721600
  ]
def negativeScales : Array ℕ := #[
    45, 17, 51, 15, 12, 17,
    18, 15, 22, 18, 47, 17,
    12, 18, 12, 17, 17, 36,
    25, 32, 32, 25, 22, 31,
    18, 34, 16, 13, 18, 19,
    16, 23, 19, 30, 18, 13,
    19, 13, 18, 18, 22, 29,
    34, 35, 26, 9, 10, 12,
    13, 9, 12, 13, 9, 10,
    9, 15, 16, 18, 19, 15,
    18, 19, 15, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    45798393141467780, 17245561990455634, 51059117029314585, 15585637432057036, 12526743743000334, 17245561990455634,
    18236401991170158, 15585637432057036, 22184359931729877, 18217905647552768, 47798394570611582, 17245561990455634,
    12526743743000334, 18217905647552768, 12526743743000334, 17245561990455634, 17245561990455634, 36851088940074721,
    25214259489651054, 32846053795925841, 32846053795925841, 25214259489651054, 22696913843508470, 31105130350989745,
    18403457303036754, 34451764744581121, 16743532744829480, 13684639055631019, 18403457303036754, 19394297303751276,
    16743532744829480, 23342255244310991, 19375800960133884, 30105134508900998, 18403457303036754, 13684639055631019,
    19375800960133884, 13684639055631019, 18403457303036754, 18403457303036754, 22696913843508470, 29997719950393266,
    34286904904549188, 35286904771876322, 26997721679668275, 9346513733165637, 10962173043893966, 12526743743000334,
    13684639055631019, 9346513733165637, 12682336269758884, 13707466985121264, 9346513733165637, 10962173043893966,
    9346513733165637, 15037675637718717, 16653334935685977, 18217905647552768, 19375800960133884, 15037675637718717,
    18373498174264463, 19398628889588149, 15037675637718717, 16653334935685977
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
noncomputable def negativeCeiling : ℝ := 18950217 / 8000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 275581375275264964085025865728, coefficient := (-275581375275264964085025865728) }, { argument := 2935290779490251114767450112, coefficient := (-2935290779490251114767450112) }, { argument := 2641347619703167865495620681728, coefficient := (-2641347619703167865495620681728) }, { argument := 1857778974360918427068006400, coefficient := (-1857778974360918427068006400) }, { argument := 111466738461655105624080384, coefficient := (-111466738461655105624080384) }, { argument := 2935290779490251114767450112, coefficient := (-2935290779490251114767450112) }, { argument := 2916712989746641930496770048, coefficient := (-2916712989746641930496770048) }, { argument := 1857778974360918427068006400, coefficient := (-1857778974360918427068006400) }, { argument := 45013984548765053487857795072, coefficient := (-45013984548765053487857795072) }, { argument := 2879557410259423561955409920, coefficient := (-2879557410259423561955409920) }, { argument := 275581648268235320045378469888, coefficient := (-275581648268235320045378469888) }, { argument := 2935290779490251114767450112, coefficient := (-2935290779490251114767450112) }, { argument := 111466738461655105624080384, coefficient := (-111466738461655105624080384) }, { argument := 2879557410259423561955409920, coefficient := (-2879557410259423561955409920) }, { argument := 111466738461655105624080384, coefficient := (-111466738461655105624080384) }, { argument := 2935290779490251114767450112, coefficient := (-2935290779490251114767450112) }, { argument := 2935290779490251114767450112, coefficient := (-2935290779490251114767450112) }, { argument := 2233072941445303556785569792, coefficient := (-2233072941445303556785569792) }, { argument := 89759032004984391388364800, coefficient := (-89759032004984391388364800) }, { argument := 17802343098291527394263040000, coefficient := (-17802343098291527394263040000) }, { argument := 17802343098291527394263040000, coefficient := (-17802343098291527394263040000) }, { argument := 89759032004984391388364800, coefficient := (-89759032004984391388364800) }, { argument := 250842773517534256718413824, coefficient := (-250842773517534256718413824) }, { argument := 42608571788872370447324282880, coefficient := (-42608571788872370447324282880) }, { argument := 3274781705943749909180055552, coefficient := (-3274781705943749909180055552) }, { argument := 433445316036094767355542896640, coefficient := (-433445316036094767355542896640) }, { argument := 2072646649331487284291174400, coefficient := (-2072646649331487284291174400) }, { argument := 124358798959889237057470464, coefficient := (-124358798959889237057470464) }, { argument := 3274781705943749909180055552, coefficient := (-3274781705943749909180055552) }, { argument := 3254055239450435036337143808, coefficient := (-3254055239450435036337143808) }, { argument := 2072646649331487284291174400, coefficient := (-2072646649331487284291174400) }, { argument := 50220228313301936898375155712, coefficient := (-50220228313301936898375155712) }, { argument := 3212602306463805290651320320, coefficient := (-3212602306463805290651320320) }, { argument := 42608694588847669131809390592, coefficient := (-42608694588847669131809390592) }, { argument := 3274781705943749909180055552, coefficient := (-3274781705943749909180055552) }, { argument := 124358798959889237057470464, coefficient := (-124358798959889237057470464) }, { argument := 3212602306463805290651320320, coefficient := (-3212602306463805290651320320) }, { argument := 124358798959889237057470464, coefficient := (-124358798959889237057470464) }, { argument := 3274781705943749909180055552, coefficient := (-3274781705943749909180055552) }, { argument := 3274781705943749909180055552, coefficient := (-3274781705943749909180055552) }, { argument := 250842773517534256718413824, coefficient := (-250842773517534256718413824) }, { argument := 4943940448589781086272225280, coefficient := (-4943940448589781086272225280) }, { argument := 193319899894225937244734095360, coefficient := (-193319899894225937244734095360) }, { argument := 193319882116176336207153725440, coefficient := (-193319882116176336207153725440) }, { argument := 4943946374606314765465681920, coefficient := (-4943946374606314765465681920) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 111466738461655105624080384, coefficient := (-111466738461655105624080384) }, { argument := 124358798959889237057470464, coefficient := (-124358798959889237057470464) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 124160459567608711958495232, coefficient := (-124160459567608711958495232) }, { argument := 126342192882694488047222784, coefficient := (-126342192882694488047222784) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 158836796651320516762664960, coefficient := (-158836796651320516762664960) }, { argument := 3894063401774309443213721600, coefficient := (-3894063401774309443213721600) }, { argument := 2879557410259423561955409920, coefficient := (-2879557410259423561955409920) }, { argument := 3212602306463805290651320320, coefficient := (-3212602306463805290651320320) }, { argument := 158836796651320516762664960, coefficient := (-158836796651320516762664960) }, { argument := 3207478538829891725594460160, coefficient := (-3207478538829891725594460160) }, { argument := 3263839982802940941219921920, coefficient := (-3263839982802940941219921920) }, { argument := 158836796651320516762664960, coefficient := (-158836796651320516762664960) }, { argument := 3894063401774309443213721600, coefficient := (-3894063401774309443213721600) }] }

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


end Parent2

namespace Parent2

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-45719639271911468198263036837888)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    33635, 19989425, 3964599375, 3964599375, 19989425, 651,
    1995, 5901, 13167, 651, 6573, 13377,
    651, 1995, 651, 19989425, 3964599375, 3964599375,
    19989425, 668577, 225991395, 17143, 2297832747, 5425,
    651, 17143, 34069, 5425, 525791, 33635,
    112996023, 17143, 651, 33635, 651, 17143,
    17143, 668577, 17143, 52535, 155393, 346731,
    17143, 173089, 352261, 17143, 52535, 17143,
    38926775, 7720535625, 7720535625, 38926775, 17143, 52535,
    155393, 346731, 17143, 173089, 352261, 17143,
    52535, 17143, 1206730025, 239336604375
  ]
def negativeCoefficients : Array ℕ := #[
    158836796651320516762664960, 92184951788902888452915200, 18283487506353460567080960000, 18283487506353460567080960000, 92184951788902888452915200, 6148521160696278068232192,
    150737938133199075221176320, 111466738461655105624080384, 124358798959889237057470464, 6148521160696278068232192, 124160459567608711958495232, 126342192882694488047222784,
    6148521160696278068232192, 150737938133199075221176320, 6148521160696278068232192, 92184951788902888452915200, 18283487506353460567080960000, 18283487506353460567080960000,
    92184951788902888452915200, 12333068812568510890770432, 2084402713212802197262172160, 161911057231668655796781056, 21193766304048994734965784576, 102475352678271301137203200,
    6148521160696278068232192, 161911057231668655796781056, 160886303704885942785409024, 102475352678271301137203200, 2482977795394513626554433536, 158836796651320516762664960,
    2084408717627998189721223168, 161911057231668655796781056, 6148521160696278068232192, 158836796651320516762664960, 6148521160696278068232192, 161911057231668655796781056,
    161911057231668655796781056, 12333068812568510890770432, 161911057231668655796781056, 3969432370840908980824309760, 2935290779490251114767450112, 3274781705943749909180055552,
    161911057231668655796781056, 3269558768613696081573707776, 3327011079244288185243533312, 161911057231668655796781056, 3969432370840908980824309760, 161911057231668655796781056,
    89759032004984391388364800, 17802343098291527394263040000, 17802343098291527394263040000, 89759032004984391388364800, 161911057231668655796781056, 3969432370840908980824309760,
    2935290779490251114767450112, 3274781705943749909180055552, 161911057231668655796781056, 3269558768613696081573707776, 3327011079244288185243533312, 161911057231668655796781056,
    3969432370840908980824309760, 161911057231668655796781056, 2782529992154516133039308800, 551872636047037349222154240000
  ]
def negativeScales : Array ℕ := #[
    15, 24, 31, 31, 24, 9,
    10, 12, 13, 9, 12, 13,
    9, 10, 9, 24, 31, 31,
    24, 19, 27, 14, 31, 12,
    9, 14, 15, 12, 19, 15,
    26, 14, 9, 15, 9, 14,
    14, 19, 14, 15, 17, 18,
    14, 17, 18, 14, 15, 14,
    25, 32, 32, 25, 14, 15,
    17, 18, 14, 17, 18, 14,
    15, 14, 30, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15037675637718717, 24252733637465689, 31884527945435175, 31884527945435175, 24252733637465689, 9346513733165637,
    10962173043893966, 12526743743000334, 13684639055631019, 9346513733165637, 12682336269758884, 13707466985121264,
    9346513733165637, 10962173043893966, 9346513733165637, 24252733637465689, 31884527945435175, 31884527945435175,
    24252733637465689, 19350734199483832, 27751692599994064, 14065331980621583, 31097626645941103, 12405407422219213,
    9346513733165637, 14065331980621583, 15056171981336107, 12405407422219213, 19004129921895826, 15037675637718717,
    26751696755874086, 14065331980621583, 9346513733165637, 15037675637718717, 9346513733165637, 14065331980621583,
    14065331980621583, 19350734199483832, 14065331980621583, 15680991278611640, 17245561990455634, 18403457303036754,
    14065331980621583, 17401154517167333, 18426285232491027, 14065331980621583, 15680991278611640, 14065331980621583,
    25214259489651054, 32846053795925841, 32846053795925841, 25214259489651054, 14065331980621583, 15680991278611640,
    17245561990455634, 18403457303036754, 14065331980621583, 17401154517167333, 18426285232491027, 14065331980621583,
    15680991278611640, 14065331980621583, 30168455800037929, 37800250105355915
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
noncomputable def negativeCeiling : ℝ := 313433049 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 158836796651320516762664960, coefficient := (-158836796651320516762664960) }, { argument := 92184951788902888452915200, coefficient := (-92184951788902888452915200) }, { argument := 18283487506353460567080960000, coefficient := (-18283487506353460567080960000) }, { argument := 18283487506353460567080960000, coefficient := (-18283487506353460567080960000) }, { argument := 92184951788902888452915200, coefficient := (-92184951788902888452915200) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 111466738461655105624080384, coefficient := (-111466738461655105624080384) }, { argument := 124358798959889237057470464, coefficient := (-124358798959889237057470464) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 124160459567608711958495232, coefficient := (-124160459567608711958495232) }, { argument := 126342192882694488047222784, coefficient := (-126342192882694488047222784) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 92184951788902888452915200, coefficient := (-92184951788902888452915200) }, { argument := 18283487506353460567080960000, coefficient := (-18283487506353460567080960000) }, { argument := 18283487506353460567080960000, coefficient := (-18283487506353460567080960000) }, { argument := 92184951788902888452915200, coefficient := (-92184951788902888452915200) }, { argument := 12333068812568510890770432, coefficient := (-12333068812568510890770432) }, { argument := 2084402713212802197262172160, coefficient := (-2084402713212802197262172160) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 21193766304048994734965784576, coefficient := (-21193766304048994734965784576) }, { argument := 102475352678271301137203200, coefficient := (-102475352678271301137203200) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 160886303704885942785409024, coefficient := (-160886303704885942785409024) }, { argument := 102475352678271301137203200, coefficient := (-102475352678271301137203200) }, { argument := 2482977795394513626554433536, coefficient := (-2482977795394513626554433536) }, { argument := 158836796651320516762664960, coefficient := (-158836796651320516762664960) }, { argument := 2084408717627998189721223168, coefficient := (-2084408717627998189721223168) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 158836796651320516762664960, coefficient := (-158836796651320516762664960) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 12333068812568510890770432, coefficient := (-12333068812568510890770432) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 3969432370840908980824309760, coefficient := (-3969432370840908980824309760) }, { argument := 2935290779490251114767450112, coefficient := (-2935290779490251114767450112) }, { argument := 3274781705943749909180055552, coefficient := (-3274781705943749909180055552) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 3269558768613696081573707776, coefficient := (-3269558768613696081573707776) }, { argument := 3327011079244288185243533312, coefficient := (-3327011079244288185243533312) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 3969432370840908980824309760, coefficient := (-3969432370840908980824309760) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 89759032004984391388364800, coefficient := (-89759032004984391388364800) }, { argument := 17802343098291527394263040000, coefficient := (-17802343098291527394263040000) }, { argument := 17802343098291527394263040000, coefficient := (-17802343098291527394263040000) }, { argument := 89759032004984391388364800, coefficient := (-89759032004984391388364800) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 3969432370840908980824309760, coefficient := (-3969432370840908980824309760) }, { argument := 2935290779490251114767450112, coefficient := (-2935290779490251114767450112) }, { argument := 3274781705943749909180055552, coefficient := (-3274781705943749909180055552) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 3269558768613696081573707776, coefficient := (-3269558768613696081573707776) }, { argument := 3327011079244288185243533312, coefficient := (-3327011079244288185243533312) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 3969432370840908980824309760, coefficient := (-3969432370840908980824309760) }, { argument := 161911057231668655796781056, coefficient := (-161911057231668655796781056) }, { argument := 2782529992154516133039308800, coefficient := (-2782529992154516133039308800) }, { argument := 551872636047037349222154240000, coefficient := (-551872636047037349222154240000) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11
