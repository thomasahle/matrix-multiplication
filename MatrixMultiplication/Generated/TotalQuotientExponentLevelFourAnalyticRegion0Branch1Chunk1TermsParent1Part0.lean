import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 1, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk1

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
def constantNumerator : ℤ := 1764773717006244768209583472640
def positiveArguments : Array ℕ := #[
    3, 148553, 7828307, 2377757, 685371, 48949461,
    48960783, 691155, 93133, 4169469, 10451605, 2084751,
    23281
  ]
def positiveCoefficients : Array ℕ := #[
    950737950171172051122527404032, 89794778640606003895063281664, 295745076755310589711143141376, 89829119689669431955057278976, 12946292154923406439024164864, 462314587961869732943298035712,
    462421521228507833189516967936, 13055548825871078550688235520, 879616315298197335374299136, 39379521313928033519007694848, 394850473153542386109529456640, 39379832990115902915591798784,
    879531312701505681760452608
  ]
def positiveScales : Array ℕ := #[
    1, 17, 22, 21, 19, 25,
    25, 19, 16, 21, 23, 20,
    14
  ]
def negativeArguments : Array ℕ := #[
    147870407283, 6612258658649, 66233488321353, 826538882107, 147856146195, 2445762711,
    5591449491489, 1398191497497, 157873012155, 147870407283, 485453699629, 4622878811,
    485453699629, 21748899322547, 218205563826385, 5437267832069, 485406729787, 5591449491489,
    49917699308025, 399433937481153, 11277249352245, 6612258658649, 21748899322547, 1653720756989,
    4622878811, 1653720756989, 33129308557811, 1653733862021, 73958927705, 1398191497497,
    399433937481153, 49940784985293, 11279882576655, 66233488321353, 218205563826385, 33129308557811,
    157873012155, 11277249352245, 11279882576655, 159217747875, 826538882107, 5437267832069,
    1653733862021, 147856146195, 485406729787, 73958927705, 3, 3,
    3
  ]
def negativeCoefficients : Array ℕ := #[
    83243638892355284732215296, 3722370703896121513489727488, 37286139165436683678054875136, 3722400201464311523754115072, 83235610613529947500707840, 88117888271170032786997248,
    3147706230791351218175213568, 3148447353560042495337824256, 88874604839139473212047360, 83243638892355284732215296, 273286137594349136535093248, 83278381162394246419841024,
    273286137594349136535093248, 12243541860592637761671921664, 122838811992334558416726917120, 12243638691209766510486618112, 273259695923983030151020544, 3147706230791351218175213568,
    112404666001406928014750515200, 112430658249953165401934266368, 3174263498783421836789022720, 3722370703896121513489727488, 12243541860592637761671921664, 3723848092475257484342198272,
    83278381162394246419841024, 3723848092475257484342198272, 37300285418999950959982936064, 3723877602383873423555166208, 83270349813239863228497920, 3148447353560042495337824256,
    112430658249953165401934266368, 112456650325177808179811057664, 3175004685562900517675335680, 37286139165436683678054875136, 122838811992334558416726917120, 37300285418999950959982936064,
    88874604839139473212047360, 3174263498783421836789022720, 3175004685562900517675335680, 89631623750077447667712000, 3722400201464311523754115072, 12243638691209766510486618112,
    3723877602383873423555166208, 83235610613529947500707840, 273259695923983030151020544, 83270349813239863228497920, 475368975085586025561263702016, 950737950171172051122527404032,
    475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    37, 42, 45, 39, 37, 31,
    42, 40, 37, 37, 38, 32,
    38, 44, 47, 42, 38, 42,
    45, 48, 43, 42, 44, 40,
    32, 40, 44, 40, 36, 40,
    48, 45, 43, 45, 47, 44,
    37, 43, 43, 37, 39, 42,
    40, 37, 38, 36, 1, 1,
    1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 17180618214860357, 22900268903797994, 21181169852612871, 19386525623047153, 25544789638097467,
    25545123294570138, 19398649763422199, 16507004830906736, 21991432229935852, 23317221170894705, 20991443648355553,
    14506865407901125
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    37105542404258858, 42588280299799793, 45912626081703559, 39588291732252421, 37105403259493471, 31187637293718364,
    42346359465206668, 40346699105634333, 37199973612312667, 37105542404258858, 38820542749236829, 32106144396732949,
    38820542749236829, 44306007623826548, 47632681216543673, 42306019033637559, 38820403155207790, 42346359465206668,
    45504616675881377, 48504950243467979, 43358480454659113, 42588280299799793, 44306007623826548, 40588852783972790,
    32106144396732949, 40588852783972790, 44913173332284351, 40588864216670655, 36106005256824313, 40346699105634333,
    48504950243467979, 45505283731724243, 43358817282924966, 45912626081703559, 47632681216543673, 44913173332284351,
    37199973612312667, 43358480454659113, 43358817282924966, 37212210204668453, 39588291732252421, 42306019033637559,
    40588864216670655, 37105403259493471, 38820403155207790, 36106005256824313, 1584962500724866, 1584962500724866,
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
noncomputable def positiveFloor : ℝ := 281536503 / 500000000000
noncomputable def negativeCeiling : ℝ := 567149561 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 83243638892355284732215296, coefficient := (-83243638892355284732215296) }, { argument := 3722370703896121513489727488, coefficient := (-3722370703896121513489727488) }, { argument := 37286139165436683678054875136, coefficient := (-37286139165436683678054875136) }, { argument := 3722400201464311523754115072, coefficient := (-3722400201464311523754115072) }, { argument := 83235610613529947500707840, coefficient := (-83235610613529947500707840) }, { argument := 88117888271170032786997248, coefficient := (-88117888271170032786997248) }, { argument := 3147706230791351218175213568, coefficient := (-3147706230791351218175213568) }, { argument := 3148447353560042495337824256, coefficient := (-3148447353560042495337824256) }, { argument := 88874604839139473212047360, coefficient := (-88874604839139473212047360) }, { argument := 83243638892355284732215296, coefficient := (-83243638892355284732215296) }, { argument := 273286137594349136535093248, coefficient := (-273286137594349136535093248) }, { argument := 83278381162394246419841024, coefficient := (-83278381162394246419841024) }, { argument := 273286137594349136535093248, coefficient := (-273286137594349136535093248) }, { argument := 12243541860592637761671921664, coefficient := (-12243541860592637761671921664) }, { argument := 122838811992334558416726917120, coefficient := (-122838811992334558416726917120) }, { argument := 12243638691209766510486618112, coefficient := (-12243638691209766510486618112) }, { argument := 273259695923983030151020544, coefficient := (-273259695923983030151020544) }, { argument := 3147706230791351218175213568, coefficient := (-3147706230791351218175213568) }, { argument := 112404666001406928014750515200, coefficient := (-112404666001406928014750515200) }, { argument := 112430658249953165401934266368, coefficient := (-112430658249953165401934266368) }, { argument := 3174263498783421836789022720, coefficient := (-3174263498783421836789022720) }, { argument := 3722370703896121513489727488, coefficient := (-3722370703896121513489727488) }, { argument := 12243541860592637761671921664, coefficient := (-12243541860592637761671921664) }, { argument := 3723848092475257484342198272, coefficient := (-3723848092475257484342198272) }, { argument := 83278381162394246419841024, coefficient := (-83278381162394246419841024) }, { argument := 3723848092475257484342198272, coefficient := (-3723848092475257484342198272) }, { argument := 37300285418999950959982936064, coefficient := (-37300285418999950959982936064) }, { argument := 3723877602383873423555166208, coefficient := (-3723877602383873423555166208) }, { argument := 83270349813239863228497920, coefficient := (-83270349813239863228497920) }, { argument := 3148447353560042495337824256, coefficient := (-3148447353560042495337824256) }, { argument := 112430658249953165401934266368, coefficient := (-112430658249953165401934266368) }, { argument := 112456650325177808179811057664, coefficient := (-112456650325177808179811057664) }, { argument := 3175004685562900517675335680, coefficient := (-3175004685562900517675335680) }, { argument := 37286139165436683678054875136, coefficient := (-37286139165436683678054875136) }, { argument := 122838811992334558416726917120, coefficient := (-122838811992334558416726917120) }, { argument := 37300285418999950959982936064, coefficient := (-37300285418999950959982936064) }, { argument := 88874604839139473212047360, coefficient := (-88874604839139473212047360) }, { argument := 3174263498783421836789022720, coefficient := (-3174263498783421836789022720) }, { argument := 3175004685562900517675335680, coefficient := (-3175004685562900517675335680) }, { argument := 89631623750077447667712000, coefficient := (-89631623750077447667712000) }, { argument := 3722400201464311523754115072, coefficient := (-3722400201464311523754115072) }, { argument := 12243638691209766510486618112, coefficient := (-12243638691209766510486618112) }, { argument := 3723877602383873423555166208, coefficient := (-3723877602383873423555166208) }, { argument := 83235610613529947500707840, coefficient := (-83235610613529947500707840) }, { argument := 273259695923983030151020544, coefficient := (-273259695923983030151020544) }, { argument := 83270349813239863228497920, coefficient := (-83270349813239863228497920) }, { argument := 950737950171172051122527404032, coefficient := 950737950171172051122527404032 }, { argument := 89794778640606003895063281664, coefficient := 89794778640606003895063281664 }, { argument := 295745076755310589711143141376, coefficient := 295745076755310589711143141376 }, { argument := 89829119689669431955057278976, coefficient := 89829119689669431955057278976 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 12946292154923406439024164864, coefficient := 12946292154923406439024164864 }, { argument := 462314587961869732943298035712, coefficient := 462314587961869732943298035712 }, { argument := 462421521228507833189516967936, coefficient := 462421521228507833189516967936 }, { argument := 13055548825871078550688235520, coefficient := 13055548825871078550688235520 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 879616315298197335374299136, coefficient := 879616315298197335374299136 }, { argument := 39379521313928033519007694848, coefficient := 39379521313928033519007694848 }, { argument := 394850473153542386109529456640, coefficient := 394850473153542386109529456640 }, { argument := 39379832990115902915591798784, coefficient := 39379832990115902915591798784 }, { argument := 879531312701505681760452608, coefficient := 879531312701505681760452608 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk1
