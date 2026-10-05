import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 2, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk2

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
def constantNumerator : ℤ := 3900096661609841387787897536512
def positiveArguments : Array ℕ := #[
    11, 8386525, 8390691, 7105025, 47072137, 14215285,
    2056851, 36710785, 36720241, 2076041, 59345, 2728855,
    27978017, 682219, 59339
  ]
def positiveCoefficients : Array ℕ := #[
    1743019575313815427057966907392, 158416978270993405303167385600, 158495671786063945071008415744, 268420255359607207875523379200, 889167528183392370561969553408, 268519141713758498246298173440,
    19426408445313825254871662592, 693447122575334913865091645440, 693625741365182975325654482944, 19607652870926362238173315072, 560497677851798190413578240, 25773306777222491379240796160,
    264244899475914285145510641664, 25773505116614771904339771392, 560441009454003754671013888
  ]
def positiveScales : Array ℕ := #[
    3, 22, 23, 22, 25, 23,
    20, 25, 25, 20, 15, 21,
    24, 19, 15
  ]
def negativeArguments : Array ℕ := #[
    497687362433, 22885407718039, 234638766873977, 5721395957767, 497637043283, 811613218195,
    231851117123785, 231911739578875, 1638598498345, 811613218195, 2690007871987, 405954049085,
    497687362433, 497956521087, 497956521087, 22897182049641, 234754467586695, 5724339564537,
    497906176941, 2690007871987, 768021870281945, 768217880898077, 10859502952633, 231851117123785,
    768021870281945, 115968275771695, 22885407718039, 22897182049641, 405954049085, 115968275771695,
    28999651147645, 3278394191605, 231911739578875, 768217880898077, 28999651147645, 234638766873977,
    234754467586695, 1638598498345, 10859502952633, 3278394191605, 5721395957767, 5724339564537,
    497637043283, 497906176941, 1, 9, 9, 1
  ]
def negativeCoefficients : Array ℕ := #[
    140086538750016486845186048, 6441669604448894599334723584, 66044941441269718611144998912, 6441719175859630817419460608, 140072375168442136839323648, 1827590493515985532076687360,
    65260287792756959394880552960, 65277351496891559934164992000, 1844897896639099076639457280, 1827590493515985532076687360, 6057359224952177052694347776, 1828254504188750042664796160,
    140086538750016486845186048, 140162300175882608361603072, 140162300175882608361603072, 6444983784162351090285674496, 66077508296687423961610321920, 6445033382447755134750425088,
    140148129558559740496183296, 6057359224952177052694347776, 216178938050884932355405905920, 216234110134495728388655808512, 6113356681363347484228714496, 65260287792756959394880552960,
    216178938050884932355405905920, 65284335444025565182259363840, 6441669604448894599334723584, 6444983784162351090285674496, 1828254504188750042664796160, 65284335444025565182259363840,
    65301409051204199340006440960, 1845571857460734558218485760, 65277351496891559934164992000, 216234110134495728388655808512, 65301409051204199340006440960, 66044941441269718611144998912,
    66077508296687423961610321920, 1844897896639099076639457280, 6113356681363347484228714496, 1845571857460734558218485760, 6441719175859630817419460608, 6445033382447755134750425088,
    140072375168442136839323648, 140148129558559740496183296, 316912650057057350374175801344, 1426106925256758076683791106048, 1426106925256758076683791106048, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    38, 44, 47, 42, 38, 39,
    47, 47, 40, 39, 41, 38,
    38, 38, 38, 44, 47, 42,
    38, 41, 49, 49, 43, 47,
    49, 46, 44, 44, 38, 46,
    44, 41, 47, 49, 44, 47,
    47, 40, 43, 41, 42, 42,
    38, 38, 0, 3, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3459431618637292, 22999641714201809, 23000358195391310, 22760408295103051, 25488370014781049, 23760939687863881,
    20972005856013423, 25129700628648956, 25130072191600617, 20985403504115962, 15856838862890622, 21379864307161366,
    24737790376322966, 19379875409429271, 15856692993687819
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    38856448799447386, 44379493228229509, 47737434722847945, 42379504330343970, 38856302927025291, 39562001405246185,
    47720192006577639, 47720569180880370, 40575599536464893, 39562001405246185, 41290747533311285, 38562525478294077,
    38856448799447386, 38857228825088519, 38857228825088519, 44380235290671704, 47738145942508687, 42380246393092975,
    38857082959091722, 41290747533311285, 49448140722309730, 49448508872587280, 43304023304985350, 47720192006577639,
    49448140722309730, 46720723524871606, 44379493228229509, 44380235290671704, 38562525478294077, 46720723524871606,
    44721100779045992, 41576126472064317, 47720569180880370, 49448508872587280, 44721100779045992, 47737434722847945,
    47738145942508687, 40575599536464893, 43304023304985350, 41576126472064317, 42379504330343970, 42380246393092975,
    38856302927025291, 38857082959091722, 0, 3169925001442313, 3169925001442313, 0
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 48
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
noncomputable def positiveFloor : ℝ := 69027207 / 62500000000
noncomputable def negativeCeiling : ℝ := 558024243 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 140086538750016486845186048, coefficient := (-140086538750016486845186048) }, { argument := 6441669604448894599334723584, coefficient := (-6441669604448894599334723584) }, { argument := 66044941441269718611144998912, coefficient := (-66044941441269718611144998912) }, { argument := 6441719175859630817419460608, coefficient := (-6441719175859630817419460608) }, { argument := 140072375168442136839323648, coefficient := (-140072375168442136839323648) }, { argument := 1827590493515985532076687360, coefficient := (-1827590493515985532076687360) }, { argument := 65260287792756959394880552960, coefficient := (-65260287792756959394880552960) }, { argument := 65277351496891559934164992000, coefficient := (-65277351496891559934164992000) }, { argument := 1844897896639099076639457280, coefficient := (-1844897896639099076639457280) }, { argument := 1827590493515985532076687360, coefficient := (-1827590493515985532076687360) }, { argument := 6057359224952177052694347776, coefficient := (-6057359224952177052694347776) }, { argument := 1828254504188750042664796160, coefficient := (-1828254504188750042664796160) }, { argument := 140086538750016486845186048, coefficient := (-140086538750016486845186048) }, { argument := 140162300175882608361603072, coefficient := (-140162300175882608361603072) }, { argument := 140162300175882608361603072, coefficient := (-140162300175882608361603072) }, { argument := 6444983784162351090285674496, coefficient := (-6444983784162351090285674496) }, { argument := 66077508296687423961610321920, coefficient := (-66077508296687423961610321920) }, { argument := 6445033382447755134750425088, coefficient := (-6445033382447755134750425088) }, { argument := 140148129558559740496183296, coefficient := (-140148129558559740496183296) }, { argument := 6057359224952177052694347776, coefficient := (-6057359224952177052694347776) }, { argument := 216178938050884932355405905920, coefficient := (-216178938050884932355405905920) }, { argument := 216234110134495728388655808512, coefficient := (-216234110134495728388655808512) }, { argument := 6113356681363347484228714496, coefficient := (-6113356681363347484228714496) }, { argument := 65260287792756959394880552960, coefficient := (-65260287792756959394880552960) }, { argument := 216178938050884932355405905920, coefficient := (-216178938050884932355405905920) }, { argument := 65284335444025565182259363840, coefficient := (-65284335444025565182259363840) }, { argument := 6441669604448894599334723584, coefficient := (-6441669604448894599334723584) }, { argument := 6444983784162351090285674496, coefficient := (-6444983784162351090285674496) }, { argument := 1828254504188750042664796160, coefficient := (-1828254504188750042664796160) }, { argument := 65284335444025565182259363840, coefficient := (-65284335444025565182259363840) }, { argument := 65301409051204199340006440960, coefficient := (-65301409051204199340006440960) }, { argument := 1845571857460734558218485760, coefficient := (-1845571857460734558218485760) }, { argument := 65277351496891559934164992000, coefficient := (-65277351496891559934164992000) }, { argument := 216234110134495728388655808512, coefficient := (-216234110134495728388655808512) }, { argument := 65301409051204199340006440960, coefficient := (-65301409051204199340006440960) }, { argument := 66044941441269718611144998912, coefficient := (-66044941441269718611144998912) }, { argument := 66077508296687423961610321920, coefficient := (-66077508296687423961610321920) }, { argument := 1844897896639099076639457280, coefficient := (-1844897896639099076639457280) }, { argument := 6113356681363347484228714496, coefficient := (-6113356681363347484228714496) }, { argument := 1845571857460734558218485760, coefficient := (-1845571857460734558218485760) }, { argument := 6441719175859630817419460608, coefficient := (-6441719175859630817419460608) }, { argument := 6445033382447755134750425088, coefficient := (-6445033382447755134750425088) }, { argument := 140072375168442136839323648, coefficient := (-140072375168442136839323648) }, { argument := 140148129558559740496183296, coefficient := (-140148129558559740496183296) }, { argument := 1743019575313815427057966907392, coefficient := 1743019575313815427057966907392 }, { argument := 158416978270993405303167385600, coefficient := 158416978270993405303167385600 }, { argument := 158495671786063945071008415744, coefficient := 158495671786063945071008415744 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 268420255359607207875523379200, coefficient := 268420255359607207875523379200 }, { argument := 889167528183392370561969553408, coefficient := 889167528183392370561969553408 }, { argument := 268519141713758498246298173440, coefficient := 268519141713758498246298173440 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 19426408445313825254871662592, coefficient := 19426408445313825254871662592 }, { argument := 693447122575334913865091645440, coefficient := 693447122575334913865091645440 }, { argument := 693625741365182975325654482944, coefficient := 693625741365182975325654482944 }, { argument := 19607652870926362238173315072, coefficient := 19607652870926362238173315072 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 560497677851798190413578240, coefficient := 560497677851798190413578240 }, { argument := 25773306777222491379240796160, coefficient := 25773306777222491379240796160 }, { argument := 264244899475914285145510641664, coefficient := 264244899475914285145510641664 }, { argument := 25773505116614771904339771392, coefficient := 25773505116614771904339771392 }, { argument := 560441009454003754671013888, coefficient := 560441009454003754671013888 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk2
