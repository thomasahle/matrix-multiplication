import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 21, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-175834299090217712772767509643264)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    78398449, 565427215, 57, 147, 123, 3441,
    140963603, 123, 111, 57, 57, 111,
    3441, 111, 19599597, 147, 16776495, 1040005845,
    109912305, 1719958095, 34782375, 4173885, 109912305, 218433315,
    34782375, 3371107785, 215650725, 4160023485, 109912305, 4173885,
    215650725, 4173885, 109912305, 109912305, 16776495, 3186319,
    558850417, 139712621, 796563, 404775, 191367225, 7264147275,
    765469425, 404775, 232123509, 2123500249, 9224432261, 22219063581,
    984061091, 18448857907, 984061091, 1916329493, 36203089611, 1916329493,
    22219063581, 36203089611, 928496241, 1916329493, 1916329493, 2123500249,
    335385, 158561415, 6018864885, 634246095
  ]
def negativeCoefficients : Array ℕ := #[
    1446196124478770523179843584, 10430291127415346489133629440, 1102540347488541807332032512, 1421696763866803909454462976, 19033328104012721726574034944, 33279309962351511921311612928,
    10401278032995983885223329792, 19033328104012721726574034944, 1073526127817790707139084288, 1102540347488541807332032512, 1102540347488541807332032512, 1073526127817790707139084288,
    33279309962351511921311612928, 1073526127817790707139084288, 1446194999227382026897195008, 1421696763866803909454462976, 2475773677750943393104527360, 38369443315754089025938391040,
    64880773148368214996193116160, 15863813397985009990379765760, 41063780473650768984932352000, 2463826828419046139095941120, 64880773148368214996193116160, 64470135343631707306343792640,
    41063780473650768984932352000, 994975400876558132504910888960, 63648859734158691926645145600, 38369444284208152895689850880, 64880773148368214996193116160, 2463826828419046139095941120,
    63648859734158691926645145600, 2463826828419046139095941120, 64880773148368214996193116160, 64880773148368214996193116160, 2475773677750943393104527360, 58777211130198144795541504,
    10308970617884861657484623872, 10308971853816714596024582144, 58775975198345206255583232, 238936986637945080171724800, 28240817789367938789985484800, 267999731391319277025676492800,
    28240837158449216185014681600, 238936986637945080171724800, 4281922964014415767922540544, 2448229102110094200640897024, 85080370571968474935237541888, 25616836214761717367681581056,
    2269090387321550722545221632, 85080340065665463038066556928, 2269090387321550722545221632, 2209377482392036229846663168, 83478641091461260792584732672, 2209377482392036229846663168,
    25616836214761717367681581056, 83478641091461260792584732672, 4281933132782086400312868864, 2209377482392036229846663168, 2209377482392036229846663168, 2448229102110094200640897024,
    12373522522322155937464320, 1462470921235125401624248320, 13878557518479033988829675520, 1462471924276834409581117440
  ]
def negativeScales : Array ℕ := #[
    26, 29, 5, 7, 6, 11,
    27, 6, 6, 5, 5, 6,
    11, 6, 24, 7, 23, 29,
    26, 30, 25, 21, 26, 27,
    25, 31, 27, 31, 26, 21,
    27, 21, 26, 26, 23, 21,
    29, 27, 19, 18, 27, 32,
    29, 18, 27, 30, 33, 34,
    29, 34, 29, 30, 35, 30,
    34, 35, 29, 30, 30, 30,
    18, 27, 32, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    26224321777198165, 29074766083372737, 5832890015409720, 7199672344836365, 6942514514520450, 11748612176955137,
    27070747463922485, 6942514514520450, 6794415866926375, 5832890015409720, 5832890015409720, 6794415866926375,
    11748612176955137, 6794415866926375, 24224320654670451, 7199672344836365, 23999938022575108, 29953944501693709,
    26711777668399659, 30679726269613952, 25051853109902018, 21992959442001347, 26711777668399659, 27702617669095896,
    25051853109902018, 31650575609600259, 27684121325451127, 31953944538107689, 26711777668399659, 21992959442001347,
    27684121325451127, 21992959442001347, 26711777668399659, 26711777668399659, 23999938022575108, 21603459279595911,
    29057886939250002, 27057887112213212, 19603428943153129, 18626760662480181, 27511768523202913, 32758146306712572,
    29511769512680913, 18626760662480181, 27790317402949296, 30983797150083517, 33102812973891522, 34371078964722357,
    29874172643394812, 34102812456600640, 29874172643394812, 30835698494166747, 35075393772598246, 30835698494166747,
    34371078964722357, 35075393772598246, 29790320829076659, 30835698494166747, 30835698494166747, 30983797150083517,
    18355458640651126, 27240466501385119, 32486844284626926, 29240467490863119
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
noncomputable def negativeCeiling : ℝ := 29373451 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1446196124478770523179843584, coefficient := (-1446196124478770523179843584) }, { argument := 10430291127415346489133629440, coefficient := (-10430291127415346489133629440) }, { argument := 1102540347488541807332032512, coefficient := (-1102540347488541807332032512) }, { argument := 1421696763866803909454462976, coefficient := (-1421696763866803909454462976) }, { argument := 19033328104012721726574034944, coefficient := (-19033328104012721726574034944) }, { argument := 33279309962351511921311612928, coefficient := (-33279309962351511921311612928) }, { argument := 10401278032995983885223329792, coefficient := (-10401278032995983885223329792) }, { argument := 19033328104012721726574034944, coefficient := (-19033328104012721726574034944) }, { argument := 1073526127817790707139084288, coefficient := (-1073526127817790707139084288) }, { argument := 1102540347488541807332032512, coefficient := (-1102540347488541807332032512) }, { argument := 1102540347488541807332032512, coefficient := (-1102540347488541807332032512) }, { argument := 1073526127817790707139084288, coefficient := (-1073526127817790707139084288) }, { argument := 33279309962351511921311612928, coefficient := (-33279309962351511921311612928) }, { argument := 1073526127817790707139084288, coefficient := (-1073526127817790707139084288) }, { argument := 1446194999227382026897195008, coefficient := (-1446194999227382026897195008) }, { argument := 1421696763866803909454462976, coefficient := (-1421696763866803909454462976) }, { argument := 2475773677750943393104527360, coefficient := (-2475773677750943393104527360) }, { argument := 38369443315754089025938391040, coefficient := (-38369443315754089025938391040) }, { argument := 64880773148368214996193116160, coefficient := (-64880773148368214996193116160) }, { argument := 15863813397985009990379765760, coefficient := (-15863813397985009990379765760) }, { argument := 41063780473650768984932352000, coefficient := (-41063780473650768984932352000) }, { argument := 2463826828419046139095941120, coefficient := (-2463826828419046139095941120) }, { argument := 64880773148368214996193116160, coefficient := (-64880773148368214996193116160) }, { argument := 64470135343631707306343792640, coefficient := (-64470135343631707306343792640) }, { argument := 41063780473650768984932352000, coefficient := (-41063780473650768984932352000) }, { argument := 994975400876558132504910888960, coefficient := (-994975400876558132504910888960) }, { argument := 63648859734158691926645145600, coefficient := (-63648859734158691926645145600) }, { argument := 38369444284208152895689850880, coefficient := (-38369444284208152895689850880) }, { argument := 64880773148368214996193116160, coefficient := (-64880773148368214996193116160) }, { argument := 2463826828419046139095941120, coefficient := (-2463826828419046139095941120) }, { argument := 63648859734158691926645145600, coefficient := (-63648859734158691926645145600) }, { argument := 2463826828419046139095941120, coefficient := (-2463826828419046139095941120) }, { argument := 64880773148368214996193116160, coefficient := (-64880773148368214996193116160) }, { argument := 64880773148368214996193116160, coefficient := (-64880773148368214996193116160) }, { argument := 2475773677750943393104527360, coefficient := (-2475773677750943393104527360) }, { argument := 58777211130198144795541504, coefficient := (-58777211130198144795541504) }, { argument := 10308970617884861657484623872, coefficient := (-10308970617884861657484623872) }, { argument := 10308971853816714596024582144, coefficient := (-10308971853816714596024582144) }, { argument := 58775975198345206255583232, coefficient := (-58775975198345206255583232) }, { argument := 238936986637945080171724800, coefficient := (-238936986637945080171724800) }, { argument := 28240817789367938789985484800, coefficient := (-28240817789367938789985484800) }, { argument := 267999731391319277025676492800, coefficient := (-267999731391319277025676492800) }, { argument := 28240837158449216185014681600, coefficient := (-28240837158449216185014681600) }, { argument := 238936986637945080171724800, coefficient := (-238936986637945080171724800) }, { argument := 4281922964014415767922540544, coefficient := (-4281922964014415767922540544) }, { argument := 2448229102110094200640897024, coefficient := (-2448229102110094200640897024) }, { argument := 85080370571968474935237541888, coefficient := (-85080370571968474935237541888) }, { argument := 25616836214761717367681581056, coefficient := (-25616836214761717367681581056) }, { argument := 2269090387321550722545221632, coefficient := (-2269090387321550722545221632) }, { argument := 85080340065665463038066556928, coefficient := (-85080340065665463038066556928) }, { argument := 2269090387321550722545221632, coefficient := (-2269090387321550722545221632) }, { argument := 2209377482392036229846663168, coefficient := (-2209377482392036229846663168) }, { argument := 83478641091461260792584732672, coefficient := (-83478641091461260792584732672) }, { argument := 2209377482392036229846663168, coefficient := (-2209377482392036229846663168) }, { argument := 25616836214761717367681581056, coefficient := (-25616836214761717367681581056) }, { argument := 83478641091461260792584732672, coefficient := (-83478641091461260792584732672) }, { argument := 4281933132782086400312868864, coefficient := (-4281933132782086400312868864) }, { argument := 2209377482392036229846663168, coefficient := (-2209377482392036229846663168) }, { argument := 2209377482392036229846663168, coefficient := (-2209377482392036229846663168) }, { argument := 2448229102110094200640897024, coefficient := (-2448229102110094200640897024) }, { argument := 12373522522322155937464320, coefficient := (-12373522522322155937464320) }, { argument := 1462470921235125401624248320, coefficient := (-1462470921235125401624248320) }, { argument := 13878557518479033988829675520, coefficient := (-13878557518479033988829675520) }, { argument := 1462471924276834409581117440, coefficient := (-1462471924276834409581117440) }] }

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


end Parent3

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1019757196413023658405351424786432)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    335385, 2106305915, 41078635745, 82157241355, 263289495, 33831249,
    404775, 335385, 4031697915, 2255175, 1082599605, 9032265,
    9032265, 6464835, 335385, 78398449, 565427215, 57,
    147, 123, 3441, 140963603, 123, 111,
    57, 57, 111, 3441, 111, 19599597,
    147, 499896855, 17484021585, 12846614625, 112034789865, 4065384375,
    487846125, 12846614625, 25530613875, 4065384375, 394017053625, 25205383125,
    69936094155, 12846614625, 487846125, 25205383125, 487846125, 12846614625,
    12846614625, 499896855, 9296365063, 41413971547, 503003703, 433331555943,
    19191840473, 4024028889, 19191840473, 37373584079, 706057710033, 37373584079,
    433331555943, 706057710033, 9296366043, 37373584079
  ]
def negativeCoefficients : Array ℕ := #[
    12373522522322155937464320, 2428405384684101535048663040, 94720885060644012720117514240, 94720850317354471392783892480, 2428416965780615310826536960, 2496305567987768777596993536,
    238936986637945080171724800, 12373522522322155937464320, 9296462452564175695726510080, 332805088531423504524902400, 2496304730966756433026088960, 333231761721848406453780480,
    333231761721848406453780480, 238510313447520178242846720, 12373522522322155937464320, 1446196124478770523179843584, 10430291127415346489133629440, 1102540347488541807332032512,
    1421696763866803909454462976, 19033328104012721726574034944, 33279309962351511921311612928, 10401278032995983885223329792, 19033328104012721726574034944, 1073526127817790707139084288,
    1102540347488541807332032512, 1102540347488541807332032512, 1073526127817790707139084288, 33279309962351511921311612928, 1073526127817790707139084288, 1446194999227382026897195008,
    1421696763866803909454462976, 9221469347437293036298567680, 161261635778854315737407815680, 236978212200949203792297984000, 258334636998935460792741396480, 149986210253765318855884800000,
    8999172615225919131353088000, 236978212200949203792297984000, 235478350098411550603739136000, 149986210253765318855884800000, 3634165874448733675878088704000, 232478625893336244226621440000,
    161261653799017432742426050560, 236978212200949203792297984000, 8999172615225919131353088000, 232478625893336244226621440000, 8999172615225919131353088000, 236978212200949203792297984000,
    236978212200949203792297984000, 9221469347437293036298567680, 85743833566467886226188795904, 95494116775424780170893983744, 148460489237907350549082144768, 999194538942859285202768756736,
    88506742377222966987657838592, 148460462121193562196041269248, 88506742377222966987657838592, 86177617577822362593245790208, 3256116469562044943388043640832, 86177617577822362593245790208,
    999194538942859285202768756736, 3256116469562044943388043640832, 85743842605372482343869087744, 86177617577822362593245790208
  ]
def negativeScales : Array ℕ := #[
    18, 30, 35, 36, 27, 25,
    18, 18, 31, 21, 30, 23,
    23, 22, 18, 26, 29, 5,
    7, 6, 11, 27, 6, 6,
    5, 5, 6, 11, 6, 24,
    7, 28, 34, 33, 36, 31,
    28, 33, 34, 31, 38, 34,
    36, 33, 28, 34, 28, 33,
    33, 28, 33, 35, 28, 38,
    34, 31, 34, 35, 39, 35,
    38, 39, 33, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    18355458640651126, 30972067854318208, 35257669218246249, 36257668689070654, 27972074734534713, 25011853104507595,
    18626760662480181, 18355458640651126, 31908740404461534, 21104807959273164, 30011852620766229, 23106656383665533,
    23106656383665533, 22624182118377635, 18355458640651126, 26224321777198165, 29074766083372737, 5832890015409720,
    7199672344836365, 6942514514520450, 11748612176955137, 27070747463922485, 6942514514520450, 6794415866926375,
    5832890015409720, 5832890015409720, 6794415866926375, 11748612176955137, 6794415866926375, 24224320654670451,
    7199672344836365, 28897055213867318, 34025318013198452, 33580669175440149, 36705155841947312, 31920744623340306,
    28861850930149023, 33580669175440149, 34571509176153911, 31920744623340306, 38519467116711624, 34553012832535459,
    36025318174412236, 33580669175440149, 28861850930149023, 34553012832535459, 28861850930149023, 33580669175440149,
    33580669175440149, 28897055213867318, 33114019577659692, 35269398510828356, 28905993784826014, 38656680343735048,
    34159774019653858, 31905993521313778, 34159774019653858, 35121299871839222, 39360995151585710, 35121299871839222,
    38656680343735048, 39360995151585710, 33114019729745056, 35121299871839222
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
noncomputable def negativeCeiling : ℝ := 7361610589 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 12373522522322155937464320, coefficient := (-12373522522322155937464320) }, { argument := 2428405384684101535048663040, coefficient := (-2428405384684101535048663040) }, { argument := 94720885060644012720117514240, coefficient := (-94720885060644012720117514240) }, { argument := 94720850317354471392783892480, coefficient := (-94720850317354471392783892480) }, { argument := 2428416965780615310826536960, coefficient := (-2428416965780615310826536960) }, { argument := 2496305567987768777596993536, coefficient := (-2496305567987768777596993536) }, { argument := 238936986637945080171724800, coefficient := (-238936986637945080171724800) }, { argument := 12373522522322155937464320, coefficient := (-12373522522322155937464320) }, { argument := 9296462452564175695726510080, coefficient := (-9296462452564175695726510080) }, { argument := 332805088531423504524902400, coefficient := (-332805088531423504524902400) }, { argument := 2496304730966756433026088960, coefficient := (-2496304730966756433026088960) }, { argument := 333231761721848406453780480, coefficient := (-333231761721848406453780480) }, { argument := 333231761721848406453780480, coefficient := (-333231761721848406453780480) }, { argument := 238510313447520178242846720, coefficient := (-238510313447520178242846720) }, { argument := 12373522522322155937464320, coefficient := (-12373522522322155937464320) }, { argument := 1446196124478770523179843584, coefficient := (-1446196124478770523179843584) }, { argument := 10430291127415346489133629440, coefficient := (-10430291127415346489133629440) }, { argument := 1102540347488541807332032512, coefficient := (-1102540347488541807332032512) }, { argument := 1421696763866803909454462976, coefficient := (-1421696763866803909454462976) }, { argument := 19033328104012721726574034944, coefficient := (-19033328104012721726574034944) }, { argument := 33279309962351511921311612928, coefficient := (-33279309962351511921311612928) }, { argument := 10401278032995983885223329792, coefficient := (-10401278032995983885223329792) }, { argument := 19033328104012721726574034944, coefficient := (-19033328104012721726574034944) }, { argument := 1073526127817790707139084288, coefficient := (-1073526127817790707139084288) }, { argument := 1102540347488541807332032512, coefficient := (-1102540347488541807332032512) }, { argument := 1102540347488541807332032512, coefficient := (-1102540347488541807332032512) }, { argument := 1073526127817790707139084288, coefficient := (-1073526127817790707139084288) }, { argument := 33279309962351511921311612928, coefficient := (-33279309962351511921311612928) }, { argument := 1073526127817790707139084288, coefficient := (-1073526127817790707139084288) }, { argument := 1446194999227382026897195008, coefficient := (-1446194999227382026897195008) }, { argument := 1421696763866803909454462976, coefficient := (-1421696763866803909454462976) }, { argument := 9221469347437293036298567680, coefficient := (-9221469347437293036298567680) }, { argument := 161261635778854315737407815680, coefficient := (-161261635778854315737407815680) }, { argument := 236978212200949203792297984000, coefficient := (-236978212200949203792297984000) }, { argument := 258334636998935460792741396480, coefficient := (-258334636998935460792741396480) }, { argument := 149986210253765318855884800000, coefficient := (-149986210253765318855884800000) }, { argument := 8999172615225919131353088000, coefficient := (-8999172615225919131353088000) }, { argument := 236978212200949203792297984000, coefficient := (-236978212200949203792297984000) }, { argument := 235478350098411550603739136000, coefficient := (-235478350098411550603739136000) }, { argument := 149986210253765318855884800000, coefficient := (-149986210253765318855884800000) }, { argument := 3634165874448733675878088704000, coefficient := (-3634165874448733675878088704000) }, { argument := 232478625893336244226621440000, coefficient := (-232478625893336244226621440000) }, { argument := 161261653799017432742426050560, coefficient := (-161261653799017432742426050560) }, { argument := 236978212200949203792297984000, coefficient := (-236978212200949203792297984000) }, { argument := 8999172615225919131353088000, coefficient := (-8999172615225919131353088000) }, { argument := 232478625893336244226621440000, coefficient := (-232478625893336244226621440000) }, { argument := 8999172615225919131353088000, coefficient := (-8999172615225919131353088000) }, { argument := 236978212200949203792297984000, coefficient := (-236978212200949203792297984000) }, { argument := 236978212200949203792297984000, coefficient := (-236978212200949203792297984000) }, { argument := 9221469347437293036298567680, coefficient := (-9221469347437293036298567680) }, { argument := 85743833566467886226188795904, coefficient := (-85743833566467886226188795904) }, { argument := 95494116775424780170893983744, coefficient := (-95494116775424780170893983744) }, { argument := 148460489237907350549082144768, coefficient := (-148460489237907350549082144768) }, { argument := 999194538942859285202768756736, coefficient := (-999194538942859285202768756736) }, { argument := 88506742377222966987657838592, coefficient := (-88506742377222966987657838592) }, { argument := 148460462121193562196041269248, coefficient := (-148460462121193562196041269248) }, { argument := 88506742377222966987657838592, coefficient := (-88506742377222966987657838592) }, { argument := 86177617577822362593245790208, coefficient := (-86177617577822362593245790208) }, { argument := 3256116469562044943388043640832, coefficient := (-3256116469562044943388043640832) }, { argument := 86177617577822362593245790208, coefficient := (-86177617577822362593245790208) }, { argument := 999194538942859285202768756736, coefficient := (-999194538942859285202768756736) }, { argument := 3256116469562044943388043640832, coefficient := (-3256116469562044943388043640832) }, { argument := 85743842605372482343869087744, coefficient := (-85743842605372482343869087744) }, { argument := 86177617577822362593245790208, coefficient := (-86177617577822362593245790208) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21
