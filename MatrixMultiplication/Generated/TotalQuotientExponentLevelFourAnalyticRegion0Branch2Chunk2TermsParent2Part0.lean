import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 2, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk2

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 26266837340135105111611223834624
def positiveArguments : Array ℕ := #[
    9, 14285, 16320517, 16324335, 113115, 213225
  ]
def positiveCoefficients : Array ℕ := #[
    713053462628379038341895553024, 4317376333298744440169431040, 154142924927808506988188401664, 154178984918271699599040184320, 4273363877678399346777784320, 2013853186619760201380659200
  ]
def positiveScales : Array ℕ := #[
    3, 13, 23, 23, 16, 17
  ]
def negativeArguments : Array ℕ := #[
    76102640727, 3758665191711, 3758144581659, 76288563823, 9124085353, 234631528993,
    1545209500997, 29266878839, 2253058637, 1359128010039, 67096992778507, 134176269825097,
    2724327538483, 234631528993, 1504285705273, 39750312736967, 6004089994879, 115846831735,
    76102640727, 1359128010039, 2718880511229, 37667681823, 2718880511229, 134225391621597,
    67103831620689, 681239744289, 1545209500997, 39750312736967, 1051534326472891, 79321286019259,
    1525024251193, 3758665191711, 67096992778507, 134225391621597, 1860169368439, 37667681823,
    1860169368439, 1859914895741, 37757629677, 29266878839, 6004089994879, 79321286019259,
    2995543725405, 57802113173, 3758144581659, 134176269825097, 67103831620689, 1859914895741,
    2253058637, 115846831735, 1525024251193, 57802113173, 1112864675, 76288563823,
    2724327538483, 681239744289, 37757629677, 1
  ]
def negativeCoefficients : Array ℕ := #[
    21420989026251745800486912, 1057970197300007094416572416, 1057823658597745061007458304, 21473321725368318860197888, 2568201712241712528621568, 66042904158890283036049408,
    869875616612429908425048064, 65903152316808927297667072, 2536718509509269402943488, 765121049945055518332551168, 37772248959370623281669341184, 37767262424141873481496133632,
    766830030446701212596174848, 66042904158890283036049408, 1693675135431561642457956352, 22377436703758157772388040704, 1690001091477249227304730624, 65215968529224818826936320,
    21420989026251745800486912, 765121049945055518332551168, 765296828577239254091956224, 21205019727746650683211776, 765296828577239254091956224, 37781088980667696564909637632,
    37776098885258435885392723968, 767007764632478095125774336, 869875616612429908425048064, 22377436703758157772388040704, 295980600054412337189534826496, 22326957134930210400086523904,
    858512331175470561247625216, 1057970197300007094416572416, 37772248959370623281669341184, 37781088980667696564909637632, 1047182259318486410322771968, 21205019727746650683211776,
    1047182259318486410322771968, 1047039003925000314727432192, 21255655867966297655476224, 65903152316808927297667072, 1690001091477249227304730624, 22326957134930210400086523904,
    1686341200688248174002831360, 65079393836787509548285952, 1057823658597745061007458304, 37767262424141873481496133632, 37776098885258435885392723968, 1047039003925000314727432192,
    2536718509509269402943488, 65215968529224818826936320, 858512331175470561247625216, 65079393836787509548285952, 2505948467821894067814400, 21473321725368318860197888,
    766830030446701212596174848, 767007764632478095125774336, 21255655867966297655476224, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    36, 41, 41, 36, 33, 37,
    40, 34, 31, 40, 45, 46,
    41, 37, 40, 45, 42, 36,
    36, 40, 41, 35, 41, 46,
    45, 39, 40, 45, 49, 46,
    40, 41, 45, 46, 40, 35,
    40, 40, 35, 34, 42, 46,
    41, 35, 41, 46, 45, 40,
    31, 36, 40, 35, 30, 36,
    41, 39, 35, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 13802213415781864, 23960183423056855, 23960520885736790, 16787430729911333, 17702017074168695
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    36147227464332378, 41773357550072372, 41773157709562902, 36150747752297349, 33087032796665889, 37771605935002618,
    40490939592026808, 34768549847207511, 31069237714922357, 40305818481987738, 45931313348808236, 46931122877610741,
    41309037303723002, 37771605935002618, 40452215739198085, 45176031444430730, 42449082740222683, 36753427632852519,
    36147227464332378, 40305818481987738, 41306149888155451, 35132608197306995, 41306149888155451, 46931650950215802,
    45931460387621836, 39309371649675862, 40490939592026808, 45176031444430730, 49901417374221333, 46172773301402110,
    40471969323486396, 41773357550072372, 45931313348808236, 46931650950215802, 40758571123630400, 35132608197306995,
    40758571123630400, 40758373748261408, 35136049147880224, 34768549847207511, 42449082740222683, 46172773301402110,
    41445955031061312, 35750403185917785, 41773157709562902, 46931122877610741, 45931460387621836, 40758373748261408,
    31069237714922357, 36753427632852519, 40471969323486396, 35750403185917785, 30051631024764846, 36150747752297349,
    41309037303723002, 39309371649675862, 35136049147880224, 0
  ]

abbrev PositiveTerm := Fin 6
abbrev NegativeTerm := Fin 58
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
noncomputable def positiveFloor : ℝ := 118141417 / 1000000000000
noncomputable def negativeCeiling : ℝ := 40839381 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 21420989026251745800486912, coefficient := (-21420989026251745800486912) }, { argument := 1057970197300007094416572416, coefficient := (-1057970197300007094416572416) }, { argument := 1057823658597745061007458304, coefficient := (-1057823658597745061007458304) }, { argument := 21473321725368318860197888, coefficient := (-21473321725368318860197888) }, { argument := 2568201712241712528621568, coefficient := (-2568201712241712528621568) }, { argument := 66042904158890283036049408, coefficient := (-66042904158890283036049408) }, { argument := 869875616612429908425048064, coefficient := (-869875616612429908425048064) }, { argument := 65903152316808927297667072, coefficient := (-65903152316808927297667072) }, { argument := 2536718509509269402943488, coefficient := (-2536718509509269402943488) }, { argument := 765121049945055518332551168, coefficient := (-765121049945055518332551168) }, { argument := 37772248959370623281669341184, coefficient := (-37772248959370623281669341184) }, { argument := 37767262424141873481496133632, coefficient := (-37767262424141873481496133632) }, { argument := 766830030446701212596174848, coefficient := (-766830030446701212596174848) }, { argument := 66042904158890283036049408, coefficient := (-66042904158890283036049408) }, { argument := 1693675135431561642457956352, coefficient := (-1693675135431561642457956352) }, { argument := 22377436703758157772388040704, coefficient := (-22377436703758157772388040704) }, { argument := 1690001091477249227304730624, coefficient := (-1690001091477249227304730624) }, { argument := 65215968529224818826936320, coefficient := (-65215968529224818826936320) }, { argument := 21420989026251745800486912, coefficient := (-21420989026251745800486912) }, { argument := 765121049945055518332551168, coefficient := (-765121049945055518332551168) }, { argument := 765296828577239254091956224, coefficient := (-765296828577239254091956224) }, { argument := 21205019727746650683211776, coefficient := (-21205019727746650683211776) }, { argument := 765296828577239254091956224, coefficient := (-765296828577239254091956224) }, { argument := 37781088980667696564909637632, coefficient := (-37781088980667696564909637632) }, { argument := 37776098885258435885392723968, coefficient := (-37776098885258435885392723968) }, { argument := 767007764632478095125774336, coefficient := (-767007764632478095125774336) }, { argument := 869875616612429908425048064, coefficient := (-869875616612429908425048064) }, { argument := 22377436703758157772388040704, coefficient := (-22377436703758157772388040704) }, { argument := 295980600054412337189534826496, coefficient := (-295980600054412337189534826496) }, { argument := 22326957134930210400086523904, coefficient := (-22326957134930210400086523904) }, { argument := 858512331175470561247625216, coefficient := (-858512331175470561247625216) }, { argument := 1057970197300007094416572416, coefficient := (-1057970197300007094416572416) }, { argument := 37772248959370623281669341184, coefficient := (-37772248959370623281669341184) }, { argument := 37781088980667696564909637632, coefficient := (-37781088980667696564909637632) }, { argument := 1047182259318486410322771968, coefficient := (-1047182259318486410322771968) }, { argument := 21205019727746650683211776, coefficient := (-21205019727746650683211776) }, { argument := 1047182259318486410322771968, coefficient := (-1047182259318486410322771968) }, { argument := 1047039003925000314727432192, coefficient := (-1047039003925000314727432192) }, { argument := 21255655867966297655476224, coefficient := (-21255655867966297655476224) }, { argument := 65903152316808927297667072, coefficient := (-65903152316808927297667072) }, { argument := 1690001091477249227304730624, coefficient := (-1690001091477249227304730624) }, { argument := 22326957134930210400086523904, coefficient := (-22326957134930210400086523904) }, { argument := 1686341200688248174002831360, coefficient := (-1686341200688248174002831360) }, { argument := 65079393836787509548285952, coefficient := (-65079393836787509548285952) }, { argument := 1057823658597745061007458304, coefficient := (-1057823658597745061007458304) }, { argument := 37767262424141873481496133632, coefficient := (-37767262424141873481496133632) }, { argument := 37776098885258435885392723968, coefficient := (-37776098885258435885392723968) }, { argument := 1047039003925000314727432192, coefficient := (-1047039003925000314727432192) }, { argument := 2536718509509269402943488, coefficient := (-2536718509509269402943488) }, { argument := 65215968529224818826936320, coefficient := (-65215968529224818826936320) }, { argument := 858512331175470561247625216, coefficient := (-858512331175470561247625216) }, { argument := 65079393836787509548285952, coefficient := (-65079393836787509548285952) }, { argument := 2505948467821894067814400, coefficient := (-2505948467821894067814400) }, { argument := 21473321725368318860197888, coefficient := (-21473321725368318860197888) }, { argument := 766830030446701212596174848, coefficient := (-766830030446701212596174848) }, { argument := 767007764632478095125774336, coefficient := (-767007764632478095125774336) }, { argument := 21255655867966297655476224, coefficient := (-21255655867966297655476224) }, { argument := 713053462628379038341895553024, coefficient := 713053462628379038341895553024 }, { argument := 4317376333298744440169431040, coefficient := 4317376333298744440169431040 }, { argument := 154142924927808506988188401664, coefficient := 154142924927808506988188401664 }, { argument := 154178984918271699599040184320, coefficient := 154178984918271699599040184320 }, { argument := 4273363877678399346777784320, coefficient := 4273363877678399346777784320 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 2013853186619760201380659200, coefficient := 2013853186619760201380659200 }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-26342128107681728572047325396992)
def positiveArguments : Array ℕ := #[
    5482923, 36254427, 2735311, 26307, 333105, 16444825,
    16442651, 333851
  ]
def positiveCoefficients : Array ℕ := #[
    51784743606710167488027426816, 684826763681777211663364128768, 51668563946498608476480077824, 1987700721037628106187210752, 3146087774552586337816412160, 155316980793313626702636646400,
    155296447943846109485247496192, 3153133545345027848475246592
  ]
def positiveScales : Array ℕ := #[
    22, 25, 21, 14, 18, 23,
    23, 18
  ]
def negativeArguments : Array ℕ := #[
    5, 1
  ]
def negativeCoefficients : Array ℕ := #[
    792281625142643375935439503360, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    22386513782463138, 25111653836469753, 21383273443530230, 14683159115245354, 18345617483871068, 23971130318902293,
    23970939582527369, 18348844836048204
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2321928094887363, 0
  ]

abbrev PositiveTerm := Fin 8
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 162811737 / 500000000000
noncomputable def negativeCeiling : ℝ := 1383977 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 51784743606710167488027426816, coefficient := 51784743606710167488027426816 }, { argument := 684826763681777211663364128768, coefficient := 684826763681777211663364128768 }, { argument := 51668563946498608476480077824, coefficient := 51668563946498608476480077824 }, { argument := 1987700721037628106187210752, coefficient := 1987700721037628106187210752 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 3146087774552586337816412160, coefficient := 3146087774552586337816412160 }, { argument := 155316980793313626702636646400, coefficient := 155316980793313626702636646400 }, { argument := 155296447943846109485247496192, coefficient := 155296447943846109485247496192 }, { argument := 3153133545345027848475246592, coefficient := 3153133545345027848475246592 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk2
