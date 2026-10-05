import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 0, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk0

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 158456325028528675187087900672
def positiveArguments : Array ℕ := #[
    1, 116249, 2039025, 8156073, 232545, 8447,
    720307, 13828403, 720313, 33785
  ]
def positiveCoefficients : Array ℕ := #[
    158456325028528675187087900672, 2195881525068453545787785216, 77032186541866226654851891200, 77031931534076151694010351616, 2196325427517843292437872640, 319118637446399144960720896,
    13606214536705542139766898688, 130605573677628100964018814976, 13606327873501131011252027392, 319090303247501927089438720
  ]
def positiveScales : Array ℕ := #[
    0, 16, 20, 22, 17, 13,
    19, 23, 19, 15
  ]
def negativeArguments : Array ℕ := #[
    981955303, 83734968443, 1607538020347, 83735665937, 3927472465, 981955303,
    17223644175, 68894348631, 1964307615, 17223644175, 1468723980675, 28196459427075,
    1468736214825, 68888459625, 83734968443, 1468723980675, 5874876474411, 167503791315,
    68894348631, 5874876474411, 112785464341419, 5874925410849, 275552926305, 1607538020347,
    28196459427075, 112785464341419, 3215725975635, 1964307615, 167503791315, 3215725975635,
    167505186585, 7856532825, 83735665937, 1468736214825, 5874925410849, 167505186585,
    3927472465, 68888459625, 275552926305, 7856532825, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    2211166768342641246470144, 94277193169443760407314432, 904963453677331752119435264, 94277978477873383696498688, 2210970441235235424174080, 2211166768342641246470144,
    77568397488492013997260800, 77568140705626160306847744, 2211613760738756929781760, 77568397488492013997260800, 3307272386039020784084582400, 31746391042235569783229644800,
    3307299934895711381461401600, 77561510274319364653056000, 94277193169443760407314432, 3307272386039020784084582400, 3307261437625634109870047232, 94296251518672415521505280,
    77568140705626160306847744, 3307261437625634109870047232, 31746285948801435777959460864, 3307288986391126814792613888, 77561253514252984076206080, 904963453677331752119435264,
    31746391042235569783229644800, 31746285948801435777959460864, 905146394099713168700866560, 2211613760738756929781760, 94296251518672415521505280, 905146394099713168700866560,
    94297036985853925675499520, 2211417393943379391283200, 94277978477873383696498688, 3307299934895711381461401600, 3307288986391126814792613888, 94297036985853925675499520,
    2210970441235235424174080, 77561510274319364653056000, 77561253514252984076206080, 2211417393943379391283200, 158456325028528675187087900672, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    29, 36, 40, 36, 31, 29,
    34, 36, 30, 34, 40, 44,
    40, 36, 36, 40, 42, 37,
    36, 42, 46, 42, 38, 40,
    44, 46, 41, 30, 37, 41,
    37, 32, 36, 40, 42, 37,
    31, 36, 38, 32, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    0, 16826858780255683, 20959448032573545, 22959443256659800, 17827150394867928, 13044223335689607,
    19458252399018136, 23721131217871558, 19458264416302702, 15044095234669214
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    29871082118590209, 36285111179342323, 40547989998204320, 36285123196626889, 31870954017563690, 29871082118590209,
    34003671369017097, 36003666593103293, 30871373733216845, 34003671369017097, 40417700432345644, 44680579251251904,
    40417712449630210, 36003543267996704, 36285111179342323, 40417700432345644, 42417695656431840, 37285402793954962,
    36003666593103293, 42417695656431840, 46680574475338094, 42417707673716406, 38003538492082900, 40547989998204320,
    44680579251251904, 46680574475338094, 41548281612816970, 30871373733216845, 37285402793954962, 41548281612816970,
    37285414811239527, 32871245632190295, 36285123196626889, 40417712449630210, 42417707673716406, 37285414811239527,
    31870954017563690, 36003543267996704, 38003538492082900, 32871245632190295, 0, 0
  ]

abbrev PositiveTerm := Fin 10
abbrev NegativeTerm := Fin 42
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
noncomputable def positiveFloor : ℝ := 21353297 / 250000000000
noncomputable def negativeCeiling : ℝ := 85413189 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2211166768342641246470144, coefficient := (-2211166768342641246470144) }, { argument := 94277193169443760407314432, coefficient := (-94277193169443760407314432) }, { argument := 904963453677331752119435264, coefficient := (-904963453677331752119435264) }, { argument := 94277978477873383696498688, coefficient := (-94277978477873383696498688) }, { argument := 2210970441235235424174080, coefficient := (-2210970441235235424174080) }, { argument := 2211166768342641246470144, coefficient := (-2211166768342641246470144) }, { argument := 77568397488492013997260800, coefficient := (-77568397488492013997260800) }, { argument := 77568140705626160306847744, coefficient := (-77568140705626160306847744) }, { argument := 2211613760738756929781760, coefficient := (-2211613760738756929781760) }, { argument := 77568397488492013997260800, coefficient := (-77568397488492013997260800) }, { argument := 3307272386039020784084582400, coefficient := (-3307272386039020784084582400) }, { argument := 31746391042235569783229644800, coefficient := (-31746391042235569783229644800) }, { argument := 3307299934895711381461401600, coefficient := (-3307299934895711381461401600) }, { argument := 77561510274319364653056000, coefficient := (-77561510274319364653056000) }, { argument := 94277193169443760407314432, coefficient := (-94277193169443760407314432) }, { argument := 3307272386039020784084582400, coefficient := (-3307272386039020784084582400) }, { argument := 3307261437625634109870047232, coefficient := (-3307261437625634109870047232) }, { argument := 94296251518672415521505280, coefficient := (-94296251518672415521505280) }, { argument := 77568140705626160306847744, coefficient := (-77568140705626160306847744) }, { argument := 3307261437625634109870047232, coefficient := (-3307261437625634109870047232) }, { argument := 31746285948801435777959460864, coefficient := (-31746285948801435777959460864) }, { argument := 3307288986391126814792613888, coefficient := (-3307288986391126814792613888) }, { argument := 77561253514252984076206080, coefficient := (-77561253514252984076206080) }, { argument := 904963453677331752119435264, coefficient := (-904963453677331752119435264) }, { argument := 31746391042235569783229644800, coefficient := (-31746391042235569783229644800) }, { argument := 31746285948801435777959460864, coefficient := (-31746285948801435777959460864) }, { argument := 905146394099713168700866560, coefficient := (-905146394099713168700866560) }, { argument := 2211613760738756929781760, coefficient := (-2211613760738756929781760) }, { argument := 94296251518672415521505280, coefficient := (-94296251518672415521505280) }, { argument := 905146394099713168700866560, coefficient := (-905146394099713168700866560) }, { argument := 94297036985853925675499520, coefficient := (-94297036985853925675499520) }, { argument := 2211417393943379391283200, coefficient := (-2211417393943379391283200) }, { argument := 94277978477873383696498688, coefficient := (-94277978477873383696498688) }, { argument := 3307299934895711381461401600, coefficient := (-3307299934895711381461401600) }, { argument := 3307288986391126814792613888, coefficient := (-3307288986391126814792613888) }, { argument := 94297036985853925675499520, coefficient := (-94297036985853925675499520) }, { argument := 2210970441235235424174080, coefficient := (-2210970441235235424174080) }, { argument := 77561510274319364653056000, coefficient := (-77561510274319364653056000) }, { argument := 77561253514252984076206080, coefficient := (-77561253514252984076206080) }, { argument := 2211417393943379391283200, coefficient := (-2211417393943379391283200) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 2195881525068453545787785216, coefficient := 2195881525068453545787785216 }, { argument := 77032186541866226654851891200, coefficient := 77032186541866226654851891200 }, { argument := 77031931534076151694010351616, coefficient := 77031931534076151694010351616 }, { argument := 2196325427517843292437872640, coefficient := 2196325427517843292437872640 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 319118637446399144960720896, coefficient := 319118637446399144960720896 }, { argument := 13606214536705542139766898688, coefficient := 13606214536705542139766898688 }, { argument := 130605573677628100964018814976, coefficient := 130605573677628100964018814976 }, { argument := 13606327873501131011252027392, coefficient := 13606327873501131011252027392 }, { argument := 319090303247501927089438720, coefficient := 319090303247501927089438720 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk0
