import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 5, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-45054792438690412467543550722048)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    66465, 2755449, 17091, 750105, 2755449, 4780374777,
    66465, 17091, 66465, 24599340197, 88351447767, 6151401505,
    156060784989, 15382739379875, 895585, 72615, 15563815, 28150415,
    15382740147875, 15563815, 459895, 459895, 895585, 895585,
    28150415, 895585, 156060016989, 72615, 158125453289, 8128383094829,
    116262531, 168818001440611, 4529709, 7549515, 231015159, 7549515,
    4529709, 3700772253, 237054771, 8128401720365, 231015159, 7549515,
    237054771, 7549515, 231015159, 7549515, 158125453289, 558261849151,
    3255, 5471853431955, 36735, 3255, 10943706967195, 3255,
    3255, 134943, 837, 36735, 134943, 558265182271,
    3255, 837, 3255, 597915
  ]
def negativeCoefficients : Array ℕ := #[
    313872088283930969128304640, 13012240002856681034433429504, 322839862234900425389113344, 3542270710632935223019438080, 13012240002856681034433429504, 11022793760966921171138248704,
    313872088283930969128304640, 322839862234900425389113344, 313872088283930969128304640, 28361108312260931498144694272, 101862284093722890470625902592, 28368332314341691685884395520,
    175708823280901873924571136, 17319424834785626178977792000, 66082509165012675136061440, 85728660538394821798133760, 1148406848462247300337500160, 2077134004294857869817282560,
    17319425699476754634113024000, 1148406848462247300337500160, 67868522926229233923522560, 67868522926229233923522560, 66082509165012675136061440, 66082509165012675136061440,
    2077134004294857869817282560, 66082509165012675136061440, 175707958589773418789339136, 85728660538394821798133760, 178033433127532792786190336, 36606983076996523451884765184,
    1072332577359361514875650048, 380144344190683778256918806528, 668467061211030554727677952, 34815992771407841392066560, 1065369378805079946597236736, 1114111768685050924546129920,
    668467061211030554727677952, 17066799656544123850391027712, 1093222173022206219710889984, 36607066958953512627643351040, 1065369378805079946597236736, 34815992771407841392066560,
    1093222173022206219710889984, 34815992771407841392066560, 1065369378805079946597236736, 1114111768685050924546129920, 178033433127532792786190336, 1257093927905803824370024448,
    15371302901740695170580480, 49286074154357015379821199360, 173476132748216416925122560, 15371302901740695170580480, 49286074619511302892782878720, 15371302901740695170580480,
    15371302901740695170580480, 637250300297878534071779328, 15810482984647572175454208, 173476132748216416925122560, 637250300297878534071779328, 1257101433424798814943838208,
    15371302901740695170580480, 15810482984647572175454208, 15371302901740695170580480, 88236679862656372435845120
  ]
def negativeScales : Array ℕ := #[
    16, 21, 14, 19, 21, 32,
    16, 14, 16, 34, 36, 32,
    37, 43, 19, 16, 23, 24,
    43, 23, 18, 18, 19, 19,
    24, 19, 37, 16, 37, 42,
    26, 47, 22, 22, 27, 22,
    22, 31, 27, 42, 27, 22,
    27, 22, 27, 22, 37, 39,
    11, 42, 15, 11, 43, 11,
    11, 17, 9, 15, 17, 39,
    11, 9, 11, 19
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16020307207094464, 21393855994216248, 14060949191591810, 19516733033214433, 21393855994216248, 32154476582594802,
    16020307207094464, 14060949191591810, 16020307207094464, 34517900569020668, 36362534724501203, 32518267998416010,
    37183317105680049, 43806377677612589, 19772470839741812, 16147979974469375, 23891692404836528, 24746652855430418,
    43806377749640708, 23891692404836528, 18810944987998023, 18810944987998023, 19772470839741812, 19772470839741812,
    24746652855430418, 19772470839741812, 37183310005930309, 16147979974469375, 37202278659263460, 42886105540709045,
    26792810980713767, 47262462078465791, 22110986940182463, 22847952536014317, 27783412282612855, 22847952536014317,
    22110986940182463, 31785179208804246, 27820645189331391, 42886108846525096, 27783412282612855, 22847952536014317,
    27820645189331391, 22847952536014317, 27783412282612855, 22847952536014317, 37202278659263460, 39022151011447726,
    11668441828086828, 42315166725629539, 15164867654172497, 11668441828086828, 43315166739245470, 11668441828086828,
    11668441828086828, 17041990615174776, 9709083812639846, 15164867654172497, 17041990615174776, 39022159625078314,
    11668441828086828, 9709083812639846, 11668441828086828, 19189580878936148
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
noncomputable def negativeCeiling : ℝ := 208123953 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 313872088283930969128304640, coefficient := (-313872088283930969128304640) }, { argument := 13012240002856681034433429504, coefficient := (-13012240002856681034433429504) }, { argument := 322839862234900425389113344, coefficient := (-322839862234900425389113344) }, { argument := 3542270710632935223019438080, coefficient := (-3542270710632935223019438080) }, { argument := 13012240002856681034433429504, coefficient := (-13012240002856681034433429504) }, { argument := 11022793760966921171138248704, coefficient := (-11022793760966921171138248704) }, { argument := 313872088283930969128304640, coefficient := (-313872088283930969128304640) }, { argument := 322839862234900425389113344, coefficient := (-322839862234900425389113344) }, { argument := 313872088283930969128304640, coefficient := (-313872088283930969128304640) }, { argument := 28361108312260931498144694272, coefficient := (-28361108312260931498144694272) }, { argument := 101862284093722890470625902592, coefficient := (-101862284093722890470625902592) }, { argument := 28368332314341691685884395520, coefficient := (-28368332314341691685884395520) }, { argument := 175708823280901873924571136, coefficient := (-175708823280901873924571136) }, { argument := 17319424834785626178977792000, coefficient := (-17319424834785626178977792000) }, { argument := 66082509165012675136061440, coefficient := (-66082509165012675136061440) }, { argument := 85728660538394821798133760, coefficient := (-85728660538394821798133760) }, { argument := 1148406848462247300337500160, coefficient := (-1148406848462247300337500160) }, { argument := 2077134004294857869817282560, coefficient := (-2077134004294857869817282560) }, { argument := 17319425699476754634113024000, coefficient := (-17319425699476754634113024000) }, { argument := 1148406848462247300337500160, coefficient := (-1148406848462247300337500160) }, { argument := 67868522926229233923522560, coefficient := (-67868522926229233923522560) }, { argument := 67868522926229233923522560, coefficient := (-67868522926229233923522560) }, { argument := 66082509165012675136061440, coefficient := (-66082509165012675136061440) }, { argument := 66082509165012675136061440, coefficient := (-66082509165012675136061440) }, { argument := 2077134004294857869817282560, coefficient := (-2077134004294857869817282560) }, { argument := 66082509165012675136061440, coefficient := (-66082509165012675136061440) }, { argument := 175707958589773418789339136, coefficient := (-175707958589773418789339136) }, { argument := 85728660538394821798133760, coefficient := (-85728660538394821798133760) }, { argument := 178033433127532792786190336, coefficient := (-178033433127532792786190336) }, { argument := 36606983076996523451884765184, coefficient := (-36606983076996523451884765184) }, { argument := 1072332577359361514875650048, coefficient := (-1072332577359361514875650048) }, { argument := 380144344190683778256918806528, coefficient := (-380144344190683778256918806528) }, { argument := 668467061211030554727677952, coefficient := (-668467061211030554727677952) }, { argument := 34815992771407841392066560, coefficient := (-34815992771407841392066560) }, { argument := 1065369378805079946597236736, coefficient := (-1065369378805079946597236736) }, { argument := 1114111768685050924546129920, coefficient := (-1114111768685050924546129920) }, { argument := 668467061211030554727677952, coefficient := (-668467061211030554727677952) }, { argument := 17066799656544123850391027712, coefficient := (-17066799656544123850391027712) }, { argument := 1093222173022206219710889984, coefficient := (-1093222173022206219710889984) }, { argument := 36607066958953512627643351040, coefficient := (-36607066958953512627643351040) }, { argument := 1065369378805079946597236736, coefficient := (-1065369378805079946597236736) }, { argument := 34815992771407841392066560, coefficient := (-34815992771407841392066560) }, { argument := 1093222173022206219710889984, coefficient := (-1093222173022206219710889984) }, { argument := 34815992771407841392066560, coefficient := (-34815992771407841392066560) }, { argument := 1065369378805079946597236736, coefficient := (-1065369378805079946597236736) }, { argument := 1114111768685050924546129920, coefficient := (-1114111768685050924546129920) }, { argument := 178033433127532792786190336, coefficient := (-178033433127532792786190336) }, { argument := 1257093927905803824370024448, coefficient := (-1257093927905803824370024448) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 49286074154357015379821199360, coefficient := (-49286074154357015379821199360) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 49286074619511302892782878720, coefficient := (-49286074619511302892782878720) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 1257101433424798814943838208, coefficient := (-1257101433424798814943838208) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 88236679862656372435845120, coefficient := (-88236679862656372435845120) }] }

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

end TermShard8


end Parent0

namespace Parent0

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 17357147293725176218495868504899584
def positiveArguments : Array ℕ := #[
    1135, 93, 105, 45, 1185, 105,
    45, 105, 105, 4353, 27, 1185,
    4353, 93, 105, 27, 105, 189,
    5481
  ]
def positiveCoefficients : Array ℕ := #[
    179847928907380046337344767262720, 3597763239173136423925579776, 4061990753905154027012751360, 3481706360490132023153786880, 45842467079786738304858193920, 4061990753905154027012751360,
    3481706360490132023153786880, 4061990753905154027012751360, 4061990753905154027012751360, 168398530969039385519871492096, 4178047632588158427784544256, 45842467079786738304858193920,
    168398530969039385519871492096, 3597763239173136423925579776, 4061990753905154027012751360, 4178047632588158427784544256, 4061990753905154027012751360, 29246333428117108994491809792,
    424071834707698080420131241984
  ]
def positiveScales : Array ℕ := #[
    10, 6, 6, 5, 10, 6,
    5, 6, 6, 12, 4, 10,
    12, 6, 6, 4, 6, 7,
    12
  ]
def negativeArguments : Array ℕ := #[
    385202385, 4096789353, 192601773, 597915, 178204527, 78855,
    27214476365, 889935, 78855, 6803621585, 78855, 78855,
    3269103, 20277, 889935, 3269103, 712828083, 78855,
    20277, 78855, 12226068497, 43911906683, 3057295005, 58168431,
    3255, 8880581005, 36735, 3255, 2220146065, 3255,
    3255, 134943, 837, 36735, 134943, 232676979,
    3255, 837, 3255, 24599340197, 88351447767, 6151401505,
    8388605, 8388611, 3
  ]
def negativeCoefficients : Array ℕ := #[
    28422919250710140319055216640, 302289698874756553099330977792, 28423004917389618626212921344, 88236679862656372435845120, 13149173209381855124445462528, 372382209006685873325998080,
    502018480605172410328379555840, 4202599215932597713250549760, 372382209006685873325998080, 502018664611444545581156925440, 372382209006685873325998080, 372382209006685873325998080,
    15437902436248605777029234688, 383021700692591183992455168, 4202599215932597713250549760, 15437902436248605777029234688, 13149357215653990377222832128, 372382209006685873325998080,
    383021700692591183992455168, 372382209006685873325998080, 28191394573975224367546630144, 101253963046239638025945481216, 28198569257532781988193239040, 536509079913116483608117248,
    15371302901740695170580480, 20477225628135170496014581760, 173476132748216416925122560, 15371302901740695170580480, 20477233133654165486588395520, 15371302901740695170580480,
    15371302901740695170580480, 637250300297878534071779328, 15810482984647572175454208, 173476132748216416925122560, 637250300297878534071779328, 536516585432111474181931008,
    15371302901740695170580480, 15810482984647572175454208, 15371302901740695170580480, 28361108312260931498144694272, 101862284093722890470625902592, 28368332314341691685884395520,
    39614067090032720187836334080, 39614095424231617405707616256, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    28, 31, 27, 19, 27, 16,
    34, 19, 16, 32, 16, 16,
    21, 14, 19, 21, 29, 16,
    14, 16, 33, 35, 31, 25,
    11, 33, 15, 11, 31, 11,
    11, 17, 9, 15, 17, 27,
    11, 9, 11, 34, 36, 32,
    22, 23, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10148476582178277, 6539158811107971, 6714245517659862, 5491853096329661, 10210671343785621, 6714245517659862,
    5491853096329661, 6714245517659862, 6714245517659862, 12087794304787900, 4754887502147955, 10210671343785621,
    12087794304787900, 6539158811107971, 6714245517659862, 4754887502147955, 6714245517659862, 7562242424220952,
    12420223419348643
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    28521041394827593, 31931846576468521, 27521045743103937, 19189580878936148, 27408958745776328, 16266914615180395,
    34663655226271635, 19763340441600069, 16266914615180395, 32663655755066686, 16266914615180395, 16266914615180395,
    21640463402318857, 14307556599677741, 19763340441600069, 21640463402318857, 29408978934352041, 16266914615180395,
    14307556599677741, 16266914615180395, 33509241503864245, 35353893127437097, 31509608621689514, 25793733055088885,
    11668441828086828, 33048006920833256, 15164867654172497, 11668441828086828, 31048007449624277, 11668441828086828,
    11668441828086828, 17041990615174776, 9709083812639846, 15164867654172497, 17041990615174776, 27793753237598046,
    11668441828086828, 9709083812639846, 11668441828086828, 34517900569020668, 36362534724501203, 32518267998416010,
    22999999507728155, 23000000515947861, 1584962500724866
  ]

abbrev PositiveTerm := Fin 19
abbrev NegativeTerm := Fin 45
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
noncomputable def positiveFloor : ℝ := 2762455651 / 125000000000
noncomputable def negativeCeiling : ℝ := 741954453 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 28422919250710140319055216640, coefficient := (-28422919250710140319055216640) }, { argument := 302289698874756553099330977792, coefficient := (-302289698874756553099330977792) }, { argument := 28423004917389618626212921344, coefficient := (-28423004917389618626212921344) }, { argument := 88236679862656372435845120, coefficient := (-88236679862656372435845120) }, { argument := 13149173209381855124445462528, coefficient := (-13149173209381855124445462528) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 502018480605172410328379555840, coefficient := (-502018480605172410328379555840) }, { argument := 4202599215932597713250549760, coefficient := (-4202599215932597713250549760) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 502018664611444545581156925440, coefficient := (-502018664611444545581156925440) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 15437902436248605777029234688, coefficient := (-15437902436248605777029234688) }, { argument := 383021700692591183992455168, coefficient := (-383021700692591183992455168) }, { argument := 4202599215932597713250549760, coefficient := (-4202599215932597713250549760) }, { argument := 15437902436248605777029234688, coefficient := (-15437902436248605777029234688) }, { argument := 13149357215653990377222832128, coefficient := (-13149357215653990377222832128) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 383021700692591183992455168, coefficient := (-383021700692591183992455168) }, { argument := 372382209006685873325998080, coefficient := (-372382209006685873325998080) }, { argument := 28191394573975224367546630144, coefficient := (-28191394573975224367546630144) }, { argument := 101253963046239638025945481216, coefficient := (-101253963046239638025945481216) }, { argument := 28198569257532781988193239040, coefficient := (-28198569257532781988193239040) }, { argument := 536509079913116483608117248, coefficient := (-536509079913116483608117248) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 20477225628135170496014581760, coefficient := (-20477225628135170496014581760) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 20477233133654165486588395520, coefficient := (-20477233133654165486588395520) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 536516585432111474181931008, coefficient := (-536516585432111474181931008) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 28361108312260931498144694272, coefficient := (-28361108312260931498144694272) }, { argument := 101862284093722890470625902592, coefficient := (-101862284093722890470625902592) }, { argument := 28368332314341691685884395520, coefficient := (-28368332314341691685884395520) }, { argument := 39614067090032720187836334080, coefficient := (-39614067090032720187836334080) }, { argument := 39614095424231617405707616256, coefficient := (-39614095424231617405707616256) }, { argument := 179847928907380046337344767262720, coefficient := 179847928907380046337344767262720 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 45842467079786738304858193920, coefficient := 45842467079786738304858193920 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 168398530969039385519871492096, coefficient := 168398530969039385519871492096 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 45842467079786738304858193920, coefficient := 45842467079786738304858193920 }, { argument := 168398530969039385519871492096, coefficient := 168398530969039385519871492096 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 29246333428117108994491809792, coefficient := 29246333428117108994491809792 }, { argument := 424071834707698080420131241984, coefficient := 424071834707698080420131241984 }] }

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

end TermShard9


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5
