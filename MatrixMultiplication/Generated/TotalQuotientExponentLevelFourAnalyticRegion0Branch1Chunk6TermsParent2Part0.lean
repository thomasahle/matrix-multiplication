import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 6, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk6

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
def constantNumerator : ℤ := (-6237650926186382824119002464256)
def positiveArguments : Array ℕ := #[
    7, 18487533, 63674697, 9250533, 887917, 32664833,
    32665355, 890759, 104715, 3910101, 42291591, 3915639,
    54801
  ]
def positiveCoefficients : Array ℕ := #[
    2218388550399401452619230609408, 174609812380293001172993703936, 601390509839360698959186100224, 174737627951518350990347599872, 33544555842961334153674489856, 1234042500221874573397033222144,
    1234062220824307037035445616640, 33651923567315858407253082112, 1978010425014779594208706560, 73859719628140330478871773184, 798865567382526166770955321344, 73964329490468858859645566976,
    2070323245021915418846035968
  ]
def positiveScales : Array ℕ := #[
    2, 24, 25, 23, 19, 24,
    24, 19, 16, 21, 25, 21,
    15
  ]
def negativeArguments : Array ℕ := #[
    646316895321, 24097673986233, 65154183466563, 1508250022665, 338304668841, 394977824045,
    7250680826009, 14501276650663, 197967235709, 646316895321, 2220648855957, 323343297801,
    2220648855957, 82988397808413, 112205686698237, 20776391173467, 1162020179709, 7250680826009,
    133373949014213, 266752332544915, 3637023722789, 24097673986233, 82988397808413, 12057573161493,
    323343297801, 12057573161493, 65202021732291, 6037369376385, 169245789741, 14501276650663,
    266752332544915, 533513499173333, 7273996094767, 65154183466563, 112205686698237, 65202021732291,
    197967235709, 3637023722789, 7273996094767, 99222685445, 1508250022665, 20776391173467,
    6037369376385, 338304668841, 1162020179709, 169245789741, 3, 1,
    3
  ]
def negativeCoefficients : Array ℕ := #[
    181922033058181966857240576, 6782892224055914609768398848, 73357089095410514532407181312, 6792554240055636146352291840, 190448597566253331111739392, 222352747648583916889047040,
    8163540866549133135489007616, 8163493015040295137083129856, 222891292242654887376060416, 181922033058181966857240576, 625057085013041465410977792, 182026094436166364836134912,
    625057085013041465410977792, 23359157340377704606023548928, 252664744401515386428274507776, 23392136886732410830253457408, 654159206041806149630558208, 8163540866549133135489007616,
    300331433540670599556260429824, 300336426362372456736316456960, 8189849341345097270450716672, 6782892224055914609768398848, 23359157340377704606023548928, 6787810249636546023643938816,
    182026094436166364836134912, 6787810249636546023643938816, 73410950194337182424795971584, 6797473618446382453217034240, 190553818902898228680720384, 8163493015040295137083129856,
    300336426362372456736316456960, 300341399509268990567064272896, 8189791525471776077258948608, 73357089095410514532407181312, 252664744401515386428274507776, 73410950194337182424795971584,
    222891292242654887376060416, 8189849341345097270450716672, 8189791525471776077258948608, 223429624598400968540815360, 6792554240055636146352291840, 23392136886732410830253457408,
    6797473618446382453217034240, 190448597566253331111739392, 654159206041806149630558208, 190553818902898228680720384, 950737950171172051122527404032, 2535301200456458802993406410752,
    950737950171172051122527404032
  ]
def negativeScales : Array ℕ := #[
    39, 44, 45, 40, 38, 38,
    42, 43, 37, 39, 41, 38,
    41, 46, 46, 44, 40, 42,
    46, 47, 41, 44, 46, 43,
    38, 43, 45, 42, 37, 43,
    47, 48, 42, 45, 46, 45,
    37, 41, 42, 36, 40, 44,
    42, 38, 40, 37, 1, 0,
    1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 24140049386729597, 25924216853159537, 23141105062985922, 19760065298196564, 24961234927368340,
    24961257982155864, 19764675629469775, 16676108591732486, 21898774442658477, 25333867499457292, 21900816331714762,
    15741914599035210
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    39233450749251553, 44453959131423519, 45888923052477665, 40456012742692710, 38299532131230690, 38522980699485698,
    42721253606748241, 43721245150204917, 37526470722594224, 39233450749251553, 41014118420853196, 38234275750545506,
    41014118420853196, 46237974888136610, 46673139123511535, 44240010315675271, 40079772261533053, 42721253606748241,
    46922470237589462, 47922494221292960, 41725895474702240, 44453959131423519, 46237974888136610, 43455004797473677,
    38234275750545506, 43455004797473677, 45889981936268421, 42457057209001755, 37300328988667130, 43721245150204917,
    47922494221292960, 48922518110089484, 42725885290025464, 45888923052477665, 46673139123511535, 45889981936268421,
    37526470722594224, 41725895474702240, 42725885290025464, 36529950952927701, 40456012742692710, 44240010315675271,
    42457057209001755, 38299532131230690, 40079772261533053, 37300328988667130, 1584962500724866, 0,
    1584962500724866
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
noncomputable def positiveFloor : ℝ := 1402958989 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1290123477 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 181922033058181966857240576, coefficient := (-181922033058181966857240576) }, { argument := 6782892224055914609768398848, coefficient := (-6782892224055914609768398848) }, { argument := 73357089095410514532407181312, coefficient := (-73357089095410514532407181312) }, { argument := 6792554240055636146352291840, coefficient := (-6792554240055636146352291840) }, { argument := 190448597566253331111739392, coefficient := (-190448597566253331111739392) }, { argument := 222352747648583916889047040, coefficient := (-222352747648583916889047040) }, { argument := 8163540866549133135489007616, coefficient := (-8163540866549133135489007616) }, { argument := 8163493015040295137083129856, coefficient := (-8163493015040295137083129856) }, { argument := 222891292242654887376060416, coefficient := (-222891292242654887376060416) }, { argument := 181922033058181966857240576, coefficient := (-181922033058181966857240576) }, { argument := 625057085013041465410977792, coefficient := (-625057085013041465410977792) }, { argument := 182026094436166364836134912, coefficient := (-182026094436166364836134912) }, { argument := 625057085013041465410977792, coefficient := (-625057085013041465410977792) }, { argument := 23359157340377704606023548928, coefficient := (-23359157340377704606023548928) }, { argument := 252664744401515386428274507776, coefficient := (-252664744401515386428274507776) }, { argument := 23392136886732410830253457408, coefficient := (-23392136886732410830253457408) }, { argument := 654159206041806149630558208, coefficient := (-654159206041806149630558208) }, { argument := 8163540866549133135489007616, coefficient := (-8163540866549133135489007616) }, { argument := 300331433540670599556260429824, coefficient := (-300331433540670599556260429824) }, { argument := 300336426362372456736316456960, coefficient := (-300336426362372456736316456960) }, { argument := 8189849341345097270450716672, coefficient := (-8189849341345097270450716672) }, { argument := 6782892224055914609768398848, coefficient := (-6782892224055914609768398848) }, { argument := 23359157340377704606023548928, coefficient := (-23359157340377704606023548928) }, { argument := 6787810249636546023643938816, coefficient := (-6787810249636546023643938816) }, { argument := 182026094436166364836134912, coefficient := (-182026094436166364836134912) }, { argument := 6787810249636546023643938816, coefficient := (-6787810249636546023643938816) }, { argument := 73410950194337182424795971584, coefficient := (-73410950194337182424795971584) }, { argument := 6797473618446382453217034240, coefficient := (-6797473618446382453217034240) }, { argument := 190553818902898228680720384, coefficient := (-190553818902898228680720384) }, { argument := 8163493015040295137083129856, coefficient := (-8163493015040295137083129856) }, { argument := 300336426362372456736316456960, coefficient := (-300336426362372456736316456960) }, { argument := 300341399509268990567064272896, coefficient := (-300341399509268990567064272896) }, { argument := 8189791525471776077258948608, coefficient := (-8189791525471776077258948608) }, { argument := 73357089095410514532407181312, coefficient := (-73357089095410514532407181312) }, { argument := 252664744401515386428274507776, coefficient := (-252664744401515386428274507776) }, { argument := 73410950194337182424795971584, coefficient := (-73410950194337182424795971584) }, { argument := 222891292242654887376060416, coefficient := (-222891292242654887376060416) }, { argument := 8189849341345097270450716672, coefficient := (-8189849341345097270450716672) }, { argument := 8189791525471776077258948608, coefficient := (-8189791525471776077258948608) }, { argument := 223429624598400968540815360, coefficient := (-223429624598400968540815360) }, { argument := 6792554240055636146352291840, coefficient := (-6792554240055636146352291840) }, { argument := 23392136886732410830253457408, coefficient := (-23392136886732410830253457408) }, { argument := 6797473618446382453217034240, coefficient := (-6797473618446382453217034240) }, { argument := 190448597566253331111739392, coefficient := (-190448597566253331111739392) }, { argument := 654159206041806149630558208, coefficient := (-654159206041806149630558208) }, { argument := 190553818902898228680720384, coefficient := (-190553818902898228680720384) }, { argument := 2218388550399401452619230609408, coefficient := 2218388550399401452619230609408 }, { argument := 174609812380293001172993703936, coefficient := 174609812380293001172993703936 }, { argument := 601390509839360698959186100224, coefficient := 601390509839360698959186100224 }, { argument := 174737627951518350990347599872, coefficient := 174737627951518350990347599872 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 33544555842961334153674489856, coefficient := 33544555842961334153674489856 }, { argument := 1234042500221874573397033222144, coefficient := 1234042500221874573397033222144 }, { argument := 1234062220824307037035445616640, coefficient := 1234062220824307037035445616640 }, { argument := 33651923567315858407253082112, coefficient := 33651923567315858407253082112 }, { argument := 2535301200456458802993406410752, coefficient := (-2535301200456458802993406410752) }, { argument := 1978010425014779594208706560, coefficient := 1978010425014779594208706560 }, { argument := 73859719628140330478871773184, coefficient := 73859719628140330478871773184 }, { argument := 798865567382526166770955321344, coefficient := 798865567382526166770955321344 }, { argument := 73964329490468858859645566976, coefficient := 73964329490468858859645566976 }, { argument := 2070323245021915418846035968, coefficient := 2070323245021915418846035968 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk6
