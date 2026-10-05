import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 0, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk0

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
def constantNumerator : ℤ := (-122518313592014567098617983664128)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    42083, 8346525, 8346525, 42083, 135997875, 872746335,
    385, 8630870225, 15, 25, 765, 25,
    15, 12255, 785, 872746335, 765, 25,
    785, 25, 765, 25, 135997875, 308150163,
    338204685, 316806933, 3816881445, 338204685, 316806891, 338204685,
    338204685, 14020999941, 86966919, 3816881445, 14020999941, 308150163,
    338204685, 86966919, 338204685, 11125325, 455806625, 9385411375,
    455806625, 11125325, 717886407, 7175241339, 14350479171, 717886407,
    616914429, 2974100829, 77172277, 20658863227, 4790617503, 4941254985,
    4790617503, 4992452689, 2974100829, 148408225, 18627791, 186183907,
    372367723, 18627791, 338204685, 2463997445
  ]
def negativeCoefficients : Array ℕ := #[
    198731348698603279527968768, 39415349908433565517244006400, 39415349908433565517244006400, 198731348698603279527968768, 627179498673335596744704000, 16099328283012981027357327360,
    14893966097652231432380088320, 79605727086987487170317516800, 9284550294640352061743431680, 483570327845851669882470400, 14797252032083061098403594240, 15474250491067253436239052800,
    9284550294640352061743431680, 237046174710036488576386990080, 15184108294359742434309570560, 16099328283012981027357327360, 14797252032083061098403594240, 483570327845851669882470400,
    15184108294359742434309570560, 483570327845851669882470400, 14797252032083061098403594240, 15474250491067253436239052800, 627179498673335596744704000, 5684367193132882345127313408,
    6238775268724555685780520960, 11688112827655697960540307456, 70409035175605699882380165120, 6238775268724555685780520960, 11688111278129195768937971712, 6238775268724555685780520960,
    6238775268724555685780520960, 258641797569123722859072454656, 6417025990688114419659964416, 70409035175605699882380165120, 258641797569123722859072454656, 5684367193132882345127313408,
    6238775268724555685780520960, 6417025990688114419659964416, 6238775268724555685780520960, 51306505752960679333068800, 8408148158476301952352256000, 86565140830553732091478016000,
    8408148158476301952352256000, 51306505752960679333068800, 3310666705980973292797820928, 132359840647634037834277453824, 132359808301268304584578695168, 3310666705980973292797820928,
    5690031293570830973515333632, 3428904802623150910397743104, 177947155425552741856968704, 23818047675139902084902551552, 5523205939554656256868220928, 5696879131952283085292175360,
    5523205939554656256868220928, 5755906065880379073142718464, 3428904802623150910397743104, 171103034063031482554777600, 171811046617775061103280128, 6868973766144680606170087424,
    6868972087490969898600890368, 171811046617775061103280128, 6238775268724555685780520960, 22726365133094613426959810560
  ]
def negativeScales : Array ℕ := #[
    15, 22, 22, 15, 27, 29,
    8, 33, 3, 4, 9, 4,
    3, 13, 9, 29, 9, 4,
    9, 4, 9, 4, 27, 28,
    28, 28, 31, 28, 28, 28,
    28, 33, 26, 31, 33, 28,
    28, 26, 28, 23, 28, 33,
    28, 23, 29, 32, 33, 29,
    29, 31, 26, 34, 32, 32,
    32, 32, 31, 27, 24, 27,
    28, 24, 28, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15360949934247380, 22992744259995894, 22992744259995894, 15360949934247380, 27019008868288388, 29700987152528297,
    8588714635586389, 33006858883378581, 3906890600547867, 4643856189792934, 9579315937583171, 4643856189792934,
    3906890600547867, 13581082863757523, 9616548843787871, 29700987152528297, 9579315937583171, 4643856189792934,
    9616548843787871, 4643856189792934, 9579315937583171, 4643856189792934, 27019008868288388, 28199058313337758,
    28333321404001886, 28239028666786856, 31829747231292150, 28333321404001886, 28239028475524641, 28333321404001886,
    28333321404001886, 33706870191208677, 26373963388499234, 31829747231292150, 33706870191208677, 28199058313337758,
    28333321404001886, 26373963388499234, 28333321404001886, 23407344145822237, 28763846653257832, 33127772835661011,
    28763846653257832, 23407344145822237, 29419180339884460, 32740380211771605, 33740379859202826, 29419180339884460,
    29200495148929183, 31469806412954510, 26201579337900298, 34266041819635619, 32157564483036986, 32202230359499130,
    32157564483036986, 32217101610014350, 31469806412954510, 27144995809533930, 24150953264830330, 27472153136535616,
    28472152783966839, 24150953264830330, 28333321404001886, 31198353614041909
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
noncomputable def negativeCeiling : ℝ := 23871827 / 40000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 198731348698603279527968768, coefficient := (-198731348698603279527968768) }, { argument := 39415349908433565517244006400, coefficient := (-39415349908433565517244006400) }, { argument := 39415349908433565517244006400, coefficient := (-39415349908433565517244006400) }, { argument := 198731348698603279527968768, coefficient := (-198731348698603279527968768) }, { argument := 627179498673335596744704000, coefficient := (-627179498673335596744704000) }, { argument := 16099328283012981027357327360, coefficient := (-16099328283012981027357327360) }, { argument := 14893966097652231432380088320, coefficient := (-14893966097652231432380088320) }, { argument := 79605727086987487170317516800, coefficient := (-79605727086987487170317516800) }, { argument := 9284550294640352061743431680, coefficient := (-9284550294640352061743431680) }, { argument := 483570327845851669882470400, coefficient := (-483570327845851669882470400) }, { argument := 14797252032083061098403594240, coefficient := (-14797252032083061098403594240) }, { argument := 15474250491067253436239052800, coefficient := (-15474250491067253436239052800) }, { argument := 9284550294640352061743431680, coefficient := (-9284550294640352061743431680) }, { argument := 237046174710036488576386990080, coefficient := (-237046174710036488576386990080) }, { argument := 15184108294359742434309570560, coefficient := (-15184108294359742434309570560) }, { argument := 16099328283012981027357327360, coefficient := (-16099328283012981027357327360) }, { argument := 14797252032083061098403594240, coefficient := (-14797252032083061098403594240) }, { argument := 483570327845851669882470400, coefficient := (-483570327845851669882470400) }, { argument := 15184108294359742434309570560, coefficient := (-15184108294359742434309570560) }, { argument := 483570327845851669882470400, coefficient := (-483570327845851669882470400) }, { argument := 14797252032083061098403594240, coefficient := (-14797252032083061098403594240) }, { argument := 15474250491067253436239052800, coefficient := (-15474250491067253436239052800) }, { argument := 627179498673335596744704000, coefficient := (-627179498673335596744704000) }, { argument := 5684367193132882345127313408, coefficient := (-5684367193132882345127313408) }, { argument := 6238775268724555685780520960, coefficient := (-6238775268724555685780520960) }, { argument := 11688112827655697960540307456, coefficient := (-11688112827655697960540307456) }, { argument := 70409035175605699882380165120, coefficient := (-70409035175605699882380165120) }, { argument := 6238775268724555685780520960, coefficient := (-6238775268724555685780520960) }, { argument := 11688111278129195768937971712, coefficient := (-11688111278129195768937971712) }, { argument := 6238775268724555685780520960, coefficient := (-6238775268724555685780520960) }, { argument := 6238775268724555685780520960, coefficient := (-6238775268724555685780520960) }, { argument := 258641797569123722859072454656, coefficient := (-258641797569123722859072454656) }, { argument := 6417025990688114419659964416, coefficient := (-6417025990688114419659964416) }, { argument := 70409035175605699882380165120, coefficient := (-70409035175605699882380165120) }, { argument := 258641797569123722859072454656, coefficient := (-258641797569123722859072454656) }, { argument := 5684367193132882345127313408, coefficient := (-5684367193132882345127313408) }, { argument := 6238775268724555685780520960, coefficient := (-6238775268724555685780520960) }, { argument := 6417025990688114419659964416, coefficient := (-6417025990688114419659964416) }, { argument := 6238775268724555685780520960, coefficient := (-6238775268724555685780520960) }, { argument := 51306505752960679333068800, coefficient := (-51306505752960679333068800) }, { argument := 8408148158476301952352256000, coefficient := (-8408148158476301952352256000) }, { argument := 86565140830553732091478016000, coefficient := (-86565140830553732091478016000) }, { argument := 8408148158476301952352256000, coefficient := (-8408148158476301952352256000) }, { argument := 51306505752960679333068800, coefficient := (-51306505752960679333068800) }, { argument := 3310666705980973292797820928, coefficient := (-3310666705980973292797820928) }, { argument := 132359840647634037834277453824, coefficient := (-132359840647634037834277453824) }, { argument := 132359808301268304584578695168, coefficient := (-132359808301268304584578695168) }, { argument := 3310666705980973292797820928, coefficient := (-3310666705980973292797820928) }, { argument := 5690031293570830973515333632, coefficient := (-5690031293570830973515333632) }, { argument := 3428904802623150910397743104, coefficient := (-3428904802623150910397743104) }, { argument := 177947155425552741856968704, coefficient := (-177947155425552741856968704) }, { argument := 23818047675139902084902551552, coefficient := (-23818047675139902084902551552) }, { argument := 5523205939554656256868220928, coefficient := (-5523205939554656256868220928) }, { argument := 5696879131952283085292175360, coefficient := (-5696879131952283085292175360) }, { argument := 5523205939554656256868220928, coefficient := (-5523205939554656256868220928) }, { argument := 5755906065880379073142718464, coefficient := (-5755906065880379073142718464) }, { argument := 3428904802623150910397743104, coefficient := (-3428904802623150910397743104) }, { argument := 171103034063031482554777600, coefficient := (-171103034063031482554777600) }, { argument := 171811046617775061103280128, coefficient := (-171811046617775061103280128) }, { argument := 6868973766144680606170087424, coefficient := (-6868973766144680606170087424) }, { argument := 6868972087490969898600890368, coefficient := (-6868972087490969898600890368) }, { argument := 171811046617775061103280128, coefficient := (-171811046617775061103280128) }, { argument := 6238775268724555685780520960, coefficient := (-6238775268724555685780520960) }, { argument := 22726365133094613426959810560, coefficient := (-22726365133094613426959810560) }] }

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
def constantNumerator : ℤ := (-355481161411030930796572372369408)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    676409825, 123414963, 11125325, 123414963, 11125325, 135997875,
    872746335, 385, 8630870225, 15, 25, 765,
    25, 15, 12255, 785, 872746335, 765,
    25, 785, 25, 765, 25, 135997875,
    5137132347, 2463997445, 4387735063, 27807971165, 2463997445, 17550936479,
    2463997445, 2463997445, 102150294077, 633599343, 27807971165, 102150294077,
    5137132347, 2463997445, 633599343, 2463997445, 10092027, 29725999833,
    771333329, 36204662107, 47881999731, 2642893025, 47881999731, 49899333053,
    29725999833, 1483333325, 1156355949, 11557724073, 23115442497, 1156355949,
    3816881445, 27807971165, 7633768025, 827133279, 455806625, 827133279,
    455806625, 338204685, 2463997445, 676409825
  ]
def negativeCoefficients : Array ℕ := #[
    6238779465358832454703513600, 569151059331833396358807552, 51306505752960679333068800, 569151059331833396358807552, 51306505752960679333068800, 627179498673335596744704000,
    16099328283012981027357327360, 14893966097652231432380088320, 79605727086987487170317516800, 9284550294640352061743431680, 483570327845851669882470400, 14797252032083061098403594240,
    15474250491067253436239052800, 9284550294640352061743431680, 237046174710036488576386990080, 15184108294359742434309570560, 16099328283012981027357327360, 14797252032083061098403594240,
    483570327845851669882470400, 15184108294359742434309570560, 483570327845851669882470400, 14797252032083061098403594240, 15474250491067253436239052800, 627179498673335596744704000,
    23690841419470972472354930688, 22726365133094613426959810560, 161878851540805712207063023616, 256483263644924922961403576320, 22726365133094613426959810560, 161878816741023017153993900032,
    22726365133094613426959810560, 22726365133094613426959810560, 942170165946293830929105289216, 23375689851183030953444376576, 256483263644924922961403576320, 942170165946293830929105289216,
    23690841419470972472354930688, 22726365133094613426959810560, 23375689851183030953444376576, 22726365133094613426959810560, 11914562512253874244260200448, 137086977813620967756930220032,
    7114294257792704913533304832, 166964534040739754578938953728, 220816748693796648662360653824, 12188192811591764960450969600, 220816748693796648662360653824, 230120056569371724318519590912,
    137086977813620967756930220032, 6840667555569908570705100800, 5332750562328633627321040896, 213202378049182971122279251968, 213202325946354334929650712576, 5332750562328633627321040896,
    70409035175605699882380165120, 256483263644924922961403576320, 70409082537621109131653939200, 15257915912561199121761828864, 8408148158476301952352256000, 15257915912561199121761828864,
    8408148158476301952352256000, 6238775268724555685780520960, 22726365133094613426959810560, 6238779465358832454703513600
  ]
def negativeScales : Array ℕ := #[
    29, 26, 23, 26, 23, 27,
    29, 8, 33, 3, 4, 9,
    4, 3, 13, 9, 29, 9,
    4, 9, 4, 9, 4, 27,
    32, 31, 32, 34, 31, 34,
    31, 31, 36, 29, 34, 36,
    32, 31, 29, 31, 23, 34,
    29, 35, 35, 31, 35, 35,
    34, 30, 30, 33, 34, 30,
    31, 34, 32, 29, 28, 29,
    28, 28, 31, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    29333322374458612, 26878942081502675, 23407344145822237, 26878942081502675, 23407344145822237, 27019008868288388,
    29700987152528297, 8588714635586389, 33006858883378581, 3906890600547867, 4643856189792934, 9579315937583171,
    4643856189792934, 3906890600547867, 13581082863757523, 9616548843787871, 29700987152528297, 9579315937583171,
    4643856189792934, 9616548843787871, 4643856189792934, 9579315937583171, 4643856189792934, 27019008868288388,
    32258316096038085, 31198353614041909, 32030829270603535, 34694779440225398, 31198353614041909, 34030828960461235,
    31198353614041909, 31198353614041909, 36571902401166234, 29238995598539255, 34694779440225398, 36571902401166234,
    32258316096038085, 31198353614041909, 29238995598539255, 31198353614041909, 23266712635399981, 34791006285196795,
    29522779209606050, 35075456435286357, 35478764354742299, 31299470884934201, 35478764354742299, 35538301481720461,
    34791006285196795, 30466195681239197, 30106938409967018, 33428138281672220, 34428137929103443, 30106938409967018,
    31829747231292150, 34694779440225398, 32829748201748899, 29623544573947581, 28763846653257832, 29623544573947581,
    28763846653257832, 28333321404001886, 31198353614041909, 29333322374458612
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
noncomputable def negativeCeiling : ℝ := 1105549719 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 6238779465358832454703513600, coefficient := (-6238779465358832454703513600) }, { argument := 569151059331833396358807552, coefficient := (-569151059331833396358807552) }, { argument := 51306505752960679333068800, coefficient := (-51306505752960679333068800) }, { argument := 569151059331833396358807552, coefficient := (-569151059331833396358807552) }, { argument := 51306505752960679333068800, coefficient := (-51306505752960679333068800) }, { argument := 627179498673335596744704000, coefficient := (-627179498673335596744704000) }, { argument := 16099328283012981027357327360, coefficient := (-16099328283012981027357327360) }, { argument := 14893966097652231432380088320, coefficient := (-14893966097652231432380088320) }, { argument := 79605727086987487170317516800, coefficient := (-79605727086987487170317516800) }, { argument := 9284550294640352061743431680, coefficient := (-9284550294640352061743431680) }, { argument := 483570327845851669882470400, coefficient := (-483570327845851669882470400) }, { argument := 14797252032083061098403594240, coefficient := (-14797252032083061098403594240) }, { argument := 15474250491067253436239052800, coefficient := (-15474250491067253436239052800) }, { argument := 9284550294640352061743431680, coefficient := (-9284550294640352061743431680) }, { argument := 237046174710036488576386990080, coefficient := (-237046174710036488576386990080) }, { argument := 15184108294359742434309570560, coefficient := (-15184108294359742434309570560) }, { argument := 16099328283012981027357327360, coefficient := (-16099328283012981027357327360) }, { argument := 14797252032083061098403594240, coefficient := (-14797252032083061098403594240) }, { argument := 483570327845851669882470400, coefficient := (-483570327845851669882470400) }, { argument := 15184108294359742434309570560, coefficient := (-15184108294359742434309570560) }, { argument := 483570327845851669882470400, coefficient := (-483570327845851669882470400) }, { argument := 14797252032083061098403594240, coefficient := (-14797252032083061098403594240) }, { argument := 15474250491067253436239052800, coefficient := (-15474250491067253436239052800) }, { argument := 627179498673335596744704000, coefficient := (-627179498673335596744704000) }, { argument := 23690841419470972472354930688, coefficient := (-23690841419470972472354930688) }, { argument := 22726365133094613426959810560, coefficient := (-22726365133094613426959810560) }, { argument := 161878851540805712207063023616, coefficient := (-161878851540805712207063023616) }, { argument := 256483263644924922961403576320, coefficient := (-256483263644924922961403576320) }, { argument := 22726365133094613426959810560, coefficient := (-22726365133094613426959810560) }, { argument := 161878816741023017153993900032, coefficient := (-161878816741023017153993900032) }, { argument := 22726365133094613426959810560, coefficient := (-22726365133094613426959810560) }, { argument := 22726365133094613426959810560, coefficient := (-22726365133094613426959810560) }, { argument := 942170165946293830929105289216, coefficient := (-942170165946293830929105289216) }, { argument := 23375689851183030953444376576, coefficient := (-23375689851183030953444376576) }, { argument := 256483263644924922961403576320, coefficient := (-256483263644924922961403576320) }, { argument := 942170165946293830929105289216, coefficient := (-942170165946293830929105289216) }, { argument := 23690841419470972472354930688, coefficient := (-23690841419470972472354930688) }, { argument := 22726365133094613426959810560, coefficient := (-22726365133094613426959810560) }, { argument := 23375689851183030953444376576, coefficient := (-23375689851183030953444376576) }, { argument := 22726365133094613426959810560, coefficient := (-22726365133094613426959810560) }, { argument := 11914562512253874244260200448, coefficient := (-11914562512253874244260200448) }, { argument := 137086977813620967756930220032, coefficient := (-137086977813620967756930220032) }, { argument := 7114294257792704913533304832, coefficient := (-7114294257792704913533304832) }, { argument := 166964534040739754578938953728, coefficient := (-166964534040739754578938953728) }, { argument := 220816748693796648662360653824, coefficient := (-220816748693796648662360653824) }, { argument := 12188192811591764960450969600, coefficient := (-12188192811591764960450969600) }, { argument := 220816748693796648662360653824, coefficient := (-220816748693796648662360653824) }, { argument := 230120056569371724318519590912, coefficient := (-230120056569371724318519590912) }, { argument := 137086977813620967756930220032, coefficient := (-137086977813620967756930220032) }, { argument := 6840667555569908570705100800, coefficient := (-6840667555569908570705100800) }, { argument := 5332750562328633627321040896, coefficient := (-5332750562328633627321040896) }, { argument := 213202378049182971122279251968, coefficient := (-213202378049182971122279251968) }, { argument := 213202325946354334929650712576, coefficient := (-213202325946354334929650712576) }, { argument := 5332750562328633627321040896, coefficient := (-5332750562328633627321040896) }, { argument := 70409035175605699882380165120, coefficient := (-70409035175605699882380165120) }, { argument := 256483263644924922961403576320, coefficient := (-256483263644924922961403576320) }, { argument := 70409082537621109131653939200, coefficient := (-70409082537621109131653939200) }, { argument := 15257915912561199121761828864, coefficient := (-15257915912561199121761828864) }, { argument := 8408148158476301952352256000, coefficient := (-8408148158476301952352256000) }, { argument := 15257915912561199121761828864, coefficient := (-15257915912561199121761828864) }, { argument := 8408148158476301952352256000, coefficient := (-8408148158476301952352256000) }, { argument := 6238775268724555685780520960, coefficient := (-6238775268724555685780520960) }, { argument := 22726365133094613426959810560, coefficient := (-22726365133094613426959810560) }, { argument := 6238779465358832454703513600, coefficient := (-6238779465358832454703513600) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk0
