import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 4, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk4

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
def constantNumerator : ℤ := (-2371162356607546556664168579072)
def positiveArguments : Array ℕ := #[
    21, 7783001, 26373431, 486663, 2508989, 179494927,
    179529725, 2528061, 19339, 3311915, 70322025, 207111,
    157961
  ]
def positiveCoefficients : Array ℕ := #[
    3327582825599102178928845914112, 294033464468327452542729453568, 996360052741402160303133687808, 294169733075557139025015865344, 47393462237954513100263653376, 1695281654219867436296525840384,
    1695610312037609232124818227200, 47753722132199672594326093824, 2922427053190914201205342208, 125120611120905768223343902720, 1328345495470085049834641817600, 125190917713102731501285408768,
    2983798928002288110402535424
  ]
def positiveScales : Array ℕ := #[
    4, 22, 24, 18, 21, 27,
    27, 21, 14, 21, 26, 17,
    17
  ]
def negativeArguments : Array ℕ := #[
    241477149013, 10308238287091, 109466488661029, 10314200479081, 123342164501, 142918772555,
    10235459813719, 20475057033253, 576198643713, 241477149013, 407368850497, 241603470889,
    407368850497, 17471625371327, 185460319937109, 34962545315097, 831574915133, 10235459813719,
    366118365259575, 1464757093605321, 41252767284735, 10308238287091, 17471625371327, 10313224298895,
    241603470889, 10313224298895, 109516772955953, 5159594966719, 246813664153, 20475057033253,
    1464757093605321, 366260181356403, 41261041648161, 109466488661029, 185460319937109, 109516772955953,
    576198643713, 41252767284735, 41261041648161, 580722348015, 10314200479081, 34962545315097,
    5159594966719, 123342164501, 831574915133, 246813664153, 5, 11,
    5
  ]
def negativeCoefficients : Array ℕ := #[
    271879099578359133987930112, 11606044527147326891867766784, 123248309385841707504784900096, 11612757358553445730871148544, 277741863042887009852981248, 321824465411473335270768640,
    11524103250757643700489158656, 11526432403168483015902887936, 324370999639656498469011456, 271879099578359133987930112, 917313101650318247126368256, 272021325366779719488372736,
    917313101650318247126368256, 39342602755932590504302084096, 417619513880388531276881068032, 39364326513248732464470294528, 936270119480907658787028992, 11524103250757643700489158656,
    412212633339129279508434124800, 412292468809325899060479000576, 11611621710720895878860636160, 11606044527147326891867766784, 39342602755932590504302084096, 11611658277372966715502100480,
    272021325366779719488372736, 11611658277372966715502100480, 123304924468812286135654940672, 11618374984749187555301261312, 277887481477349386561257472, 11526432403168483015902887936,
    412292468809325899060479000576, 412372304069336709253375721472, 11613950736973524732651503616, 123248309385841707504784900096, 417619513880388531276881068032, 123304924468812286135654940672,
    324370999639656498469011456, 11611621710720895878860636160, 11613950736973524732651503616, 326917618765759187181895680, 11612757358553445730871148544, 39364326513248732464470294528,
    11618374984749187555301261312, 277741863042887009852981248, 936270119480907658787028992, 277887481477349386561257472, 1584563250285286751870879006720, 3486039150627630854115933814784,
    1584563250285286751870879006720
  ]
def negativeScales : Array ℕ := #[
    37, 43, 46, 43, 36, 37,
    43, 44, 39, 37, 38, 37,
    38, 43, 47, 44, 39, 43,
    48, 50, 45, 43, 43, 43,
    37, 43, 46, 42, 37, 44,
    50, 48, 45, 46, 47, 46,
    39, 45, 45, 39, 43, 44,
    42, 36, 39, 37, 2, 3,
    2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4392317422778759, 22891895111578946, 24652581932215720, 18892563567811020, 21258674714969530, 27419367829356886,
    27419647492059212, 21269599844285293, 14239225576001204, 21659234215996668, 26067473279280369, 17660044653894114,
    17269208880612298
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    37813095717865004, 43228863025829494, 46637482608839843, 43229697226396554, 36843875114448828, 37056404472393653,
    43218641148410118, 44218932704033334, 39067775308370481, 37813095717865004, 38567544712452887, 37813850225265225,
    38567544712452887, 43990079080993299, 47398103877244568, 44990875472576666, 39597055283012193, 43218641148410118,
    48379303472468071, 50379582860035229, 45229556133840957, 43228863025829494, 43990079080993299, 43229560677086152,
    37813850225265225, 43229560677086152, 46638145170020914, 42230394955761819, 37844631312826076, 44218932704033334,
    50379582860035229, 48379862192772248, 45229845476516458, 46637482608839843, 47398103877244568, 46638145170020914,
    39067775308370481, 45229556133840957, 45229845476516458, 39079057598294152, 43229697226396554, 44990875472576666,
    42230394955761819, 36843875114448828, 39597055283012193, 37844631312826076, 2321928094887363, 3459431618637364,
    2321928094887363
  ]

abbrev PositiveTerm := Fin 13
abbrev NegativeTerm := Fin 49
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
noncomputable def positiveFloor : ℝ := 280023759 / 125000000000
noncomputable def negativeCeiling : ℝ := 2152585979 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 271879099578359133987930112, coefficient := (-271879099578359133987930112) }, { argument := 11606044527147326891867766784, coefficient := (-11606044527147326891867766784) }, { argument := 123248309385841707504784900096, coefficient := (-123248309385841707504784900096) }, { argument := 11612757358553445730871148544, coefficient := (-11612757358553445730871148544) }, { argument := 277741863042887009852981248, coefficient := (-277741863042887009852981248) }, { argument := 321824465411473335270768640, coefficient := (-321824465411473335270768640) }, { argument := 11524103250757643700489158656, coefficient := (-11524103250757643700489158656) }, { argument := 11526432403168483015902887936, coefficient := (-11526432403168483015902887936) }, { argument := 324370999639656498469011456, coefficient := (-324370999639656498469011456) }, { argument := 271879099578359133987930112, coefficient := (-271879099578359133987930112) }, { argument := 917313101650318247126368256, coefficient := (-917313101650318247126368256) }, { argument := 272021325366779719488372736, coefficient := (-272021325366779719488372736) }, { argument := 917313101650318247126368256, coefficient := (-917313101650318247126368256) }, { argument := 39342602755932590504302084096, coefficient := (-39342602755932590504302084096) }, { argument := 417619513880388531276881068032, coefficient := (-417619513880388531276881068032) }, { argument := 39364326513248732464470294528, coefficient := (-39364326513248732464470294528) }, { argument := 936270119480907658787028992, coefficient := (-936270119480907658787028992) }, { argument := 11524103250757643700489158656, coefficient := (-11524103250757643700489158656) }, { argument := 412212633339129279508434124800, coefficient := (-412212633339129279508434124800) }, { argument := 412292468809325899060479000576, coefficient := (-412292468809325899060479000576) }, { argument := 11611621710720895878860636160, coefficient := (-11611621710720895878860636160) }, { argument := 11606044527147326891867766784, coefficient := (-11606044527147326891867766784) }, { argument := 39342602755932590504302084096, coefficient := (-39342602755932590504302084096) }, { argument := 11611658277372966715502100480, coefficient := (-11611658277372966715502100480) }, { argument := 272021325366779719488372736, coefficient := (-272021325366779719488372736) }, { argument := 11611658277372966715502100480, coefficient := (-11611658277372966715502100480) }, { argument := 123304924468812286135654940672, coefficient := (-123304924468812286135654940672) }, { argument := 11618374984749187555301261312, coefficient := (-11618374984749187555301261312) }, { argument := 277887481477349386561257472, coefficient := (-277887481477349386561257472) }, { argument := 11526432403168483015902887936, coefficient := (-11526432403168483015902887936) }, { argument := 412292468809325899060479000576, coefficient := (-412292468809325899060479000576) }, { argument := 412372304069336709253375721472, coefficient := (-412372304069336709253375721472) }, { argument := 11613950736973524732651503616, coefficient := (-11613950736973524732651503616) }, { argument := 123248309385841707504784900096, coefficient := (-123248309385841707504784900096) }, { argument := 417619513880388531276881068032, coefficient := (-417619513880388531276881068032) }, { argument := 123304924468812286135654940672, coefficient := (-123304924468812286135654940672) }, { argument := 324370999639656498469011456, coefficient := (-324370999639656498469011456) }, { argument := 11611621710720895878860636160, coefficient := (-11611621710720895878860636160) }, { argument := 11613950736973524732651503616, coefficient := (-11613950736973524732651503616) }, { argument := 326917618765759187181895680, coefficient := (-326917618765759187181895680) }, { argument := 11612757358553445730871148544, coefficient := (-11612757358553445730871148544) }, { argument := 39364326513248732464470294528, coefficient := (-39364326513248732464470294528) }, { argument := 11618374984749187555301261312, coefficient := (-11618374984749187555301261312) }, { argument := 277741863042887009852981248, coefficient := (-277741863042887009852981248) }, { argument := 936270119480907658787028992, coefficient := (-936270119480907658787028992) }, { argument := 277887481477349386561257472, coefficient := (-277887481477349386561257472) }, { argument := 3327582825599102178928845914112, coefficient := 3327582825599102178928845914112 }, { argument := 294033464468327452542729453568, coefficient := 294033464468327452542729453568 }, { argument := 996360052741402160303133687808, coefficient := 996360052741402160303133687808 }, { argument := 294169733075557139025015865344, coefficient := 294169733075557139025015865344 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }, { argument := 47393462237954513100263653376, coefficient := 47393462237954513100263653376 }, { argument := 1695281654219867436296525840384, coefficient := 1695281654219867436296525840384 }, { argument := 1695610312037609232124818227200, coefficient := 1695610312037609232124818227200 }, { argument := 47753722132199672594326093824, coefficient := 47753722132199672594326093824 }, { argument := 3486039150627630854115933814784, coefficient := (-3486039150627630854115933814784) }, { argument := 2922427053190914201205342208, coefficient := 2922427053190914201205342208 }, { argument := 125120611120905768223343902720, coefficient := 125120611120905768223343902720 }, { argument := 1328345495470085049834641817600, coefficient := 1328345495470085049834641817600 }, { argument := 125190917713102731501285408768, coefficient := 125190917713102731501285408768 }, { argument := 2983798928002288110402535424, coefficient := 2983798928002288110402535424 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk4
