import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 17, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4424028175304222416477412587995136)
def positiveArguments : Array ℕ := #[
    483, 93, 1929, 969, 93, 1113,
    93, 19485, 15155, 2165, 20351, 240315,
    16887, 15155, 240315, 2165, 16887, 16887,
    16887, 16887, 16887, 19485, 20351, 3155,
    13251, 57421, 1893, 1893, 4417, 57421,
    57421, 1893, 708613, 28395, 13251, 57421,
    4417, 28395, 4417, 57421, 57421, 1893,
    577, 10963, 16733, 172523, 5193, 16733,
    5193, 5193, 444867, 5193, 172523, 444867,
    577, 5193, 5193, 10963, 225, 4005
  ]
def positiveCoefficients : Array ℕ := #[
    74740629871854834097034625024, 3597763239173136423925579776, 74624572993171829696262832128, 74972743629220842898578210816, 3597763239173136423925579776, 86114203982789265372670328832,
    3597763239173136423925579776, 376894713523056791506397429760, 293140332740155282282753556480, 335017523131606036894575493120, 393645589679637093351126204416, 4648368133451033761912234967040,
    10452546721706108351110755385344, 293140332740155282282753556480, 4648368133451033761912234967040, 335017523131606036894575493120, 326642085053315885972211105792, 326642085053315885972211105792,
    326642085053315885972211105792, 10452546721706108351110755385344, 326642085053315885972211105792, 376894713523056791506397429760, 393645589679637093351126204416, 244106301496585922956671057920,
    4100985865142643505672073773056, 8885469374475727595622826508288, 292927561795903107548005269504, 4686840988734449720768084312064, 341748822095220292139339481088, 8885469374475727595622826508288,
    8885469374475727595622826508288, 4686840988734449720768084312064, 109652550632266396592136639217664, 8787826853877093226440158085120, 4100985865142643505672073773056, 8885469374475727595622826508288,
    341748822095220292139339481088, 8787826853877093226440158085120, 341748822095220292139339481088, 8885469374475727595622826508288, 8885469374475727595622826508288, 292927561795903107548005269504,
    1428582805335328837233589354496, 1696442081335702994214887358464, 1294653167335141758742940352512, 13348320587351978822901350531072, 1607155656002244941887788023808, 1294653167335141758742940352512,
    1607155656002244941887788023808, 1607155656002244941887788023808, 68839833932096158344193587019776, 1607155656002244941887788023808, 13348320587351978822901350531072, 68839833932096158344193587019776,
    1428582805335328837233589354496, 1607155656002244941887788023808, 1607155656002244941887788023808, 1696442081335702994214887358464, 34817063604901320231537868800, 619743732167243500121374064640
  ]
def positiveScales : Array ℕ := #[
    8, 6, 10, 9, 6, 10,
    6, 14, 13, 11, 14, 17,
    14, 13, 17, 11, 14, 14,
    14, 14, 14, 14, 14, 11,
    13, 15, 10, 10, 12, 15,
    15, 10, 19, 14, 13, 15,
    12, 14, 12, 15, 15, 10,
    9, 13, 14, 17, 12, 14,
    12, 12, 18, 12, 17, 18,
    9, 12, 12, 13, 7, 11
  ]
def negativeArguments : Array ℕ := #[
    3, 433, 631, 577
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 34305794368676458178004530495488, 199971882186003188086104930648064, 182858599082922091165899437375488
  ]
def negativeScales : Array ℕ := #[
    1, 8, 9, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8915879378478017, 6539158811107971, 10913637427705176, 9920352855028171, 6539158811107971, 10120237877341959,
    6539158811107971, 14250076311056399, 13887506231456205, 11080151309614087, 14312812066404361, 17874567175794203,
    14043625433588973, 13887506231456205, 17874567175794203, 11080151309614087, 14043625433588973, 14043625433588973,
    14043625433588973, 14043625433588973, 14043625433588973, 14250076311056399, 14312812066404361, 11623424289869247,
    13693813617757425, 15809290835132937, 10886458695492286, 10886458695492286, 12108851117040153, 15809290835132937,
    15809290835132937, 10886458695492286, 19434638407383148, 14793349291277288, 13693813617757425, 15809290835132937,
    12108851117040153, 14793349291277288, 12108851117040153, 15809290835132937, 15809290835132937, 10886458695492286,
    9172427508645482, 13420355022089066, 14030408503773054, 17396429182843586, 12342352510087794, 14030408503773054,
    12342352510087794, 12342352510087794, 18763014558542032, 12342352510087794, 17396429182843586, 18763014558542032,
    9172427508645482, 12342352510087794, 12342352510087794, 13420355022089066, 7813781191164178, 11967586526433104
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 8758223214995597, 9301496194982550, 9172427508645483
  ]

abbrev PositiveTerm := Fin 60
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
noncomputable def positiveFloor : ℝ := 8752421911 / 100000000000
noncomputable def negativeCeiling : ℝ := 4620433761 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 74740629871854834097034625024, coefficient := 74740629871854834097034625024 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 74972743629220842898578210816, coefficient := 74972743629220842898578210816 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 86114203982789265372670328832, coefficient := 86114203982789265372670328832 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 376894713523056791506397429760, coefficient := 376894713523056791506397429760 }, { argument := 293140332740155282282753556480, coefficient := 293140332740155282282753556480 }, { argument := 335017523131606036894575493120, coefficient := 335017523131606036894575493120 }, { argument := 393645589679637093351126204416, coefficient := 393645589679637093351126204416 }, { argument := 4648368133451033761912234967040, coefficient := 4648368133451033761912234967040 }, { argument := 10452546721706108351110755385344, coefficient := 10452546721706108351110755385344 }, { argument := 293140332740155282282753556480, coefficient := 293140332740155282282753556480 }, { argument := 4648368133451033761912234967040, coefficient := 4648368133451033761912234967040 }, { argument := 335017523131606036894575493120, coefficient := 335017523131606036894575493120 }, { argument := 326642085053315885972211105792, coefficient := 326642085053315885972211105792 }, { argument := 326642085053315885972211105792, coefficient := 326642085053315885972211105792 }, { argument := 326642085053315885972211105792, coefficient := 326642085053315885972211105792 }, { argument := 10452546721706108351110755385344, coefficient := 10452546721706108351110755385344 }, { argument := 326642085053315885972211105792, coefficient := 326642085053315885972211105792 }, { argument := 376894713523056791506397429760, coefficient := 376894713523056791506397429760 }, { argument := 393645589679637093351126204416, coefficient := 393645589679637093351126204416 }, { argument := 34305794368676458178004530495488, coefficient := (-34305794368676458178004530495488) }, { argument := 244106301496585922956671057920, coefficient := 244106301496585922956671057920 }, { argument := 4100985865142643505672073773056, coefficient := 4100985865142643505672073773056 }, { argument := 8885469374475727595622826508288, coefficient := 8885469374475727595622826508288 }, { argument := 292927561795903107548005269504, coefficient := 292927561795903107548005269504 }, { argument := 4686840988734449720768084312064, coefficient := 4686840988734449720768084312064 }, { argument := 341748822095220292139339481088, coefficient := 341748822095220292139339481088 }, { argument := 8885469374475727595622826508288, coefficient := 8885469374475727595622826508288 }, { argument := 8885469374475727595622826508288, coefficient := 8885469374475727595622826508288 }, { argument := 4686840988734449720768084312064, coefficient := 4686840988734449720768084312064 }, { argument := 109652550632266396592136639217664, coefficient := 109652550632266396592136639217664 }, { argument := 8787826853877093226440158085120, coefficient := 8787826853877093226440158085120 }, { argument := 4100985865142643505672073773056, coefficient := 4100985865142643505672073773056 }, { argument := 8885469374475727595622826508288, coefficient := 8885469374475727595622826508288 }, { argument := 341748822095220292139339481088, coefficient := 341748822095220292139339481088 }, { argument := 8787826853877093226440158085120, coefficient := 8787826853877093226440158085120 }, { argument := 341748822095220292139339481088, coefficient := 341748822095220292139339481088 }, { argument := 8885469374475727595622826508288, coefficient := 8885469374475727595622826508288 }, { argument := 8885469374475727595622826508288, coefficient := 8885469374475727595622826508288 }, { argument := 292927561795903107548005269504, coefficient := 292927561795903107548005269504 }, { argument := 199971882186003188086104930648064, coefficient := (-199971882186003188086104930648064) }, { argument := 1428582805335328837233589354496, coefficient := 1428582805335328837233589354496 }, { argument := 1696442081335702994214887358464, coefficient := 1696442081335702994214887358464 }, { argument := 1294653167335141758742940352512, coefficient := 1294653167335141758742940352512 }, { argument := 13348320587351978822901350531072, coefficient := 13348320587351978822901350531072 }, { argument := 1607155656002244941887788023808, coefficient := 1607155656002244941887788023808 }, { argument := 1294653167335141758742940352512, coefficient := 1294653167335141758742940352512 }, { argument := 1607155656002244941887788023808, coefficient := 1607155656002244941887788023808 }, { argument := 1607155656002244941887788023808, coefficient := 1607155656002244941887788023808 }, { argument := 68839833932096158344193587019776, coefficient := 68839833932096158344193587019776 }, { argument := 1607155656002244941887788023808, coefficient := 1607155656002244941887788023808 }, { argument := 13348320587351978822901350531072, coefficient := 13348320587351978822901350531072 }, { argument := 68839833932096158344193587019776, coefficient := 68839833932096158344193587019776 }, { argument := 1428582805335328837233589354496, coefficient := 1428582805335328837233589354496 }, { argument := 1607155656002244941887788023808, coefficient := 1607155656002244941887788023808 }, { argument := 1607155656002244941887788023808, coefficient := 1607155656002244941887788023808 }, { argument := 1696442081335702994214887358464, coefficient := 1696442081335702994214887358464 }, { argument := 182858599082922091165899437375488, coefficient := (-182858599082922091165899437375488) }, { argument := 34817063604901320231537868800, coefficient := 34817063604901320231537868800 }, { argument := 619743732167243500121374064640, coefficient := 619743732167243500121374064640 }] }

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

end TermShard6


end Parent1

namespace Parent1

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-98163756334220755500302246527107072)
def positiveArguments : Array ℕ := #[
    225, 7125, 12165, 225, 12165, 12165,
    4005, 225, 1, 2898264497, 2898263631, 17289169907,
    123814860811, 34578337807, 762759299, 28345710461, 56689450123, 1527489397,
    40087981, 3134911759, 126392839123, 1567455887, 80168991, 12721365,
    1069409067, 534704427, 6360789, 1435659, 6952949, 1435659
  ]
def positiveCoefficients : Array ℕ := #[
    34817063604901320231537868800, 551270173744270903666016256000, 941221286119165690259240386560, 34817063604901320231537868800, 941221286119165690259240386560, 941221286119165690259240386560,
    619743732167243500121374064640, 34817063604901320231537868800, 633825300114114700748351602688, 27373334238247702803682189901824, 27373326059108954473456679780352, 163291592970910602064798934892544,
    584699148775036737990722590867456, 163291583493121070945420991004672, 28816231584757968732619729272832, 1070870664113231037065770301390848, 1070833436772662745010100273938432, 28853458925326260788289756725248,
    378620275680630325606772375552, 59216808869822091378294633005056, 596873307149190402874765484228608, 59216809153164080350473345826816, 378587356063878241309987700736, 120149895384702008367859630080,
    10100283068955397541199309963264, 10100281057227275838730448928768, 120151907112823710836720664576, 13559415884860303955699171328, 131337493258808067275689558016, 13559415884860303955699171328
  ]
def positiveScales : Array ℕ := #[
    7, 12, 13, 7, 13, 13,
    11, 7, 0, 31, 31, 34,
    36, 35, 29, 34, 35, 30,
    25, 31, 36, 30, 26, 23,
    29, 28, 22, 20, 22, 20
  ]
def negativeArguments : Array ℕ := #[
    15, 1, 691, 5751, 1735, 4519,
    129, 1
  ]
def negativeCoefficients : Array ℕ := #[
    4753689750855860255612637020160, 633825300114114700748351602688, 54746660297356657277138869682176, 911282325239068411000942516764672, 2199373791395978011596780061327360, 716064132803921083170450223136768,
    20440865928680199099134339186688, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    3, 0, 9, 12, 10, 12,
    7, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7813781191164178, 12798674298787868, 13570448699825639, 7813781191164178, 13570448699825639, 13570448699825639,
    11967586526433104, 7813781191164178, 0, 31432542115926555, 31432541684849925, 34009149552393830,
    36849393527283473, 35009149468656755, 29506652622286169, 34722411378394426, 35722361224220843, 30508515219661267,
    25256666423315664, 31545777688833353, 36879123772483649, 30545777695736395, 26256540980924766, 23600750144037487,
    29994166666467966, 28994166379118553, 22600774299579848, 20453281687963018, 22729193576691355, 20453281687963018
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    3906890600547867, 0, 9432541900388283, 12489597122389498, 10760719947749367, 12141787841671004,
    7011227255423255, 0
  ]

abbrev PositiveTerm := Fin 30
abbrev NegativeTerm := Fin 8
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
noncomputable def positiveFloor : ℝ := 332391985181 / 200000000000
noncomputable def negativeCeiling : ℝ := 21387924457 / 40000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 34817063604901320231537868800, coefficient := 34817063604901320231537868800 }, { argument := 551270173744270903666016256000, coefficient := 551270173744270903666016256000 }, { argument := 941221286119165690259240386560, coefficient := 941221286119165690259240386560 }, { argument := 34817063604901320231537868800, coefficient := 34817063604901320231537868800 }, { argument := 941221286119165690259240386560, coefficient := 941221286119165690259240386560 }, { argument := 941221286119165690259240386560, coefficient := 941221286119165690259240386560 }, { argument := 619743732167243500121374064640, coefficient := 619743732167243500121374064640 }, { argument := 34817063604901320231537868800, coefficient := 34817063604901320231537868800 }, { argument := 4753689750855860255612637020160, coefficient := (-4753689750855860255612637020160) }, { argument := 633825300114114700748351602688, coefficient := 633825300114114700748351602688 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 27373334238247702803682189901824, coefficient := 27373334238247702803682189901824 }, { argument := 27373326059108954473456679780352, coefficient := 27373326059108954473456679780352 }, { argument := 54746660297356657277138869682176, coefficient := (-54746660297356657277138869682176) }, { argument := 163291592970910602064798934892544, coefficient := 163291592970910602064798934892544 }, { argument := 584699148775036737990722590867456, coefficient := 584699148775036737990722590867456 }, { argument := 163291583493121070945420991004672, coefficient := 163291583493121070945420991004672 }, { argument := 911282325239068411000942516764672, coefficient := (-911282325239068411000942516764672) }, { argument := 28816231584757968732619729272832, coefficient := 28816231584757968732619729272832 }, { argument := 1070870664113231037065770301390848, coefficient := 1070870664113231037065770301390848 }, { argument := 1070833436772662745010100273938432, coefficient := 1070833436772662745010100273938432 }, { argument := 28853458925326260788289756725248, coefficient := 28853458925326260788289756725248 }, { argument := 2199373791395978011596780061327360, coefficient := (-2199373791395978011596780061327360) }, { argument := 378620275680630325606772375552, coefficient := 378620275680630325606772375552 }, { argument := 59216808869822091378294633005056, coefficient := 59216808869822091378294633005056 }, { argument := 596873307149190402874765484228608, coefficient := 596873307149190402874765484228608 }, { argument := 59216809153164080350473345826816, coefficient := 59216809153164080350473345826816 }, { argument := 378587356063878241309987700736, coefficient := 378587356063878241309987700736 }, { argument := 716064132803921083170450223136768, coefficient := (-716064132803921083170450223136768) }, { argument := 120149895384702008367859630080, coefficient := 120149895384702008367859630080 }, { argument := 10100283068955397541199309963264, coefficient := 10100283068955397541199309963264 }, { argument := 10100281057227275838730448928768, coefficient := 10100281057227275838730448928768 }, { argument := 120151907112823710836720664576, coefficient := 120151907112823710836720664576 }, { argument := 20440865928680199099134339186688, coefficient := (-20440865928680199099134339186688) }, { argument := 13559415884860303955699171328, coefficient := 13559415884860303955699171328 }, { argument := 131337493258808067275689558016, coefficient := 131337493258808067275689558016 }, { argument := 13559415884860303955699171328, coefficient := 13559415884860303955699171328 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end TermShard7


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17
