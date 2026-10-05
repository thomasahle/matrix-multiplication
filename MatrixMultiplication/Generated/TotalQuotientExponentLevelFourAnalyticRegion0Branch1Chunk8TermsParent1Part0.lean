import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 8, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk8

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
def constantNumerator : ℤ := 1064031268643018966243815194624
def positiveArguments : Array ℕ := #[
    3, 4587301, 31974375, 9182671, 1217481, 24559413,
    49109595, 608697, 114063, 3925227, 21119587, 1966301,
    60291
  ]
def positiveCoefficients : Array ℕ := #[
    950737950171172051122527404032, 86651665956937625433731497984, 301989433621410224359342080000, 86727875507238175768190124032, 11498782935861237048831639552, 463914195160612167866533281792,
    463827010830605428476598026240, 11497961244093217730564456448, 1077294576271120684019613696, 37072720844909937746440617984, 398937719123397926999145054208, 37142375750532265013342633984,
    1138864790474775118315782144
  ]
def positiveScales : Array ℕ := #[
    1, 22, 24, 23, 20, 24,
    25, 19, 16, 21, 24, 20,
    15
  ]
def negativeArguments : Array ℕ := #[
    174508285833, 6002218848053, 32293702536155, 3006757268153, 92246495757, 59989557525,
    9974117275167, 1246491180669, 239936762277, 174508285833, 1215267442131, 349375574811,
    1215267442131, 41834863799847, 225096404519213, 20956691459143, 642336320655, 9974117275167,
    201051218686035, 402027189868893, 4986704476143, 6002218848053, 41834863799847, 12015079732079,
    349375574811, 12015079732079, 64644063338269, 6018850602567, 184685817687, 1246491180669,
    402027189868893, 100487985646599, 9971221086879, 32293702536155, 225096404519213, 64644063338269,
    239936762277, 4986704476143, 9971221086879, 119957646831, 3006757268153, 20956691459143,
    6018850602567, 92246495757, 642336320655, 184685817687, 3, 3,
    3
  ]
def negativeCoefficients : Array ℕ := #[
    98239431381320350769872896, 3378948820935957318819905536, 36359476677060324907255070720, 3385307728111845329938153472, 103860320979364810082746368, 67542237228927733569945600,
    2807464427736983007293079552, 2806848608390759003468070912, 67536194573948780084723712, 98239431381320350769872896, 342067374971041713211047936, 98340481783198278028886016,
    342067374971041713211047936, 11775467313755400097216069632, 126718010439395762327787667456, 11797568480789358862313455616, 361603201793549179142799360, 2807464427736983007293079552,
    113181774194601416053405777920, 113160593905397134965036023808, 2807265052570549907531759616, 3378948820935957318819905536, 11775467313755400097216069632, 3381944287763611457184333824,
    98340481783198278028886016, 3381944287763611457184333824, 36391372445242876264529788928, 3388311666364928314419707904, 103968872464473569932345344, 2806848608390759003468070912,
    113160593905397134965036023808, 113139413678308751737173835776, 2806649223206068532621082624, 36359476677060324907255070720, 126718010439395762327787667456, 36391372445242876264529788928,
    67536194573948780084723712, 2807265052570549907531759616, 2806649223206068532621082624, 67530151696041645044662272, 3385307728111845329938153472, 11797568480789358862313455616,
    3388311666364928314419707904, 103860320979364810082746368, 361603201793549179142799360, 103968872464473569932345344, 475368975085586025561263702016, 950737950171172051122527404032,
    475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    37, 42, 44, 41, 36, 35,
    43, 40, 37, 37, 40, 38,
    40, 45, 47, 44, 39, 43,
    47, 48, 42, 42, 45, 43,
    38, 43, 45, 42, 37, 40,
    48, 46, 43, 44, 47, 45,
    37, 42, 43, 36, 41, 44,
    42, 36, 39, 37, 1, 1,
    1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 22129214143620023, 24930412822913595, 23130482426445543, 20215467827118719, 24549772743156132,
    25549501589088378, 19215364729860247, 16799471357406014, 21904344658018733, 24332078286839829, 20907052754362949,
    15879655037799251
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    37344504582467443, 42448633060924270, 44876318094617324, 41451345544250144, 36424775056252402, 35803992339994748,
    43181326304886504, 40181009813976672, 37803863263747932, 37344504582467443, 40144410979209992, 38345987795316234,
    40144410979209992, 45249770971704121, 47677536341171559, 44252476202689070, 39224537919136538, 43181326304886504,
    47514556409585263, 48514286405356309, 42181223846677246, 42448633060924270, 45249770971704121, 43449911455760782,
    38345987795316234, 43449911455760782, 45877583121005988, 42452625145849405, 37426282127524670, 40181009813976672,
    48514286405356309, 46514016351377953, 43180907328137742, 44876318094617324, 47677536341171559, 45877583121005988,
    37803863263747932, 42181223846677246, 43180907328137742, 36803734171189211, 41451345544250144, 44252476202689070,
    42452625145849405, 36424775056252402, 39224537919136538, 37426282127524670, 1584962500724866, 1584962500724866,
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
noncomputable def positiveFloor : ℝ := 577584967 / 1000000000000
noncomputable def negativeCeiling : ℝ := 573226643 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 98239431381320350769872896, coefficient := (-98239431381320350769872896) }, { argument := 3378948820935957318819905536, coefficient := (-3378948820935957318819905536) }, { argument := 36359476677060324907255070720, coefficient := (-36359476677060324907255070720) }, { argument := 3385307728111845329938153472, coefficient := (-3385307728111845329938153472) }, { argument := 103860320979364810082746368, coefficient := (-103860320979364810082746368) }, { argument := 67542237228927733569945600, coefficient := (-67542237228927733569945600) }, { argument := 2807464427736983007293079552, coefficient := (-2807464427736983007293079552) }, { argument := 2806848608390759003468070912, coefficient := (-2806848608390759003468070912) }, { argument := 67536194573948780084723712, coefficient := (-67536194573948780084723712) }, { argument := 98239431381320350769872896, coefficient := (-98239431381320350769872896) }, { argument := 342067374971041713211047936, coefficient := (-342067374971041713211047936) }, { argument := 98340481783198278028886016, coefficient := (-98340481783198278028886016) }, { argument := 342067374971041713211047936, coefficient := (-342067374971041713211047936) }, { argument := 11775467313755400097216069632, coefficient := (-11775467313755400097216069632) }, { argument := 126718010439395762327787667456, coefficient := (-126718010439395762327787667456) }, { argument := 11797568480789358862313455616, coefficient := (-11797568480789358862313455616) }, { argument := 361603201793549179142799360, coefficient := (-361603201793549179142799360) }, { argument := 2807464427736983007293079552, coefficient := (-2807464427736983007293079552) }, { argument := 113181774194601416053405777920, coefficient := (-113181774194601416053405777920) }, { argument := 113160593905397134965036023808, coefficient := (-113160593905397134965036023808) }, { argument := 2807265052570549907531759616, coefficient := (-2807265052570549907531759616) }, { argument := 3378948820935957318819905536, coefficient := (-3378948820935957318819905536) }, { argument := 11775467313755400097216069632, coefficient := (-11775467313755400097216069632) }, { argument := 3381944287763611457184333824, coefficient := (-3381944287763611457184333824) }, { argument := 98340481783198278028886016, coefficient := (-98340481783198278028886016) }, { argument := 3381944287763611457184333824, coefficient := (-3381944287763611457184333824) }, { argument := 36391372445242876264529788928, coefficient := (-36391372445242876264529788928) }, { argument := 3388311666364928314419707904, coefficient := (-3388311666364928314419707904) }, { argument := 103968872464473569932345344, coefficient := (-103968872464473569932345344) }, { argument := 2806848608390759003468070912, coefficient := (-2806848608390759003468070912) }, { argument := 113160593905397134965036023808, coefficient := (-113160593905397134965036023808) }, { argument := 113139413678308751737173835776, coefficient := (-113139413678308751737173835776) }, { argument := 2806649223206068532621082624, coefficient := (-2806649223206068532621082624) }, { argument := 36359476677060324907255070720, coefficient := (-36359476677060324907255070720) }, { argument := 126718010439395762327787667456, coefficient := (-126718010439395762327787667456) }, { argument := 36391372445242876264529788928, coefficient := (-36391372445242876264529788928) }, { argument := 67536194573948780084723712, coefficient := (-67536194573948780084723712) }, { argument := 2807265052570549907531759616, coefficient := (-2807265052570549907531759616) }, { argument := 2806649223206068532621082624, coefficient := (-2806649223206068532621082624) }, { argument := 67530151696041645044662272, coefficient := (-67530151696041645044662272) }, { argument := 3385307728111845329938153472, coefficient := (-3385307728111845329938153472) }, { argument := 11797568480789358862313455616, coefficient := (-11797568480789358862313455616) }, { argument := 3388311666364928314419707904, coefficient := (-3388311666364928314419707904) }, { argument := 103860320979364810082746368, coefficient := (-103860320979364810082746368) }, { argument := 361603201793549179142799360, coefficient := (-361603201793549179142799360) }, { argument := 103968872464473569932345344, coefficient := (-103968872464473569932345344) }, { argument := 950737950171172051122527404032, coefficient := 950737950171172051122527404032 }, { argument := 86651665956937625433731497984, coefficient := 86651665956937625433731497984 }, { argument := 301989433621410224359342080000, coefficient := 301989433621410224359342080000 }, { argument := 86727875507238175768190124032, coefficient := 86727875507238175768190124032 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 11498782935861237048831639552, coefficient := 11498782935861237048831639552 }, { argument := 463914195160612167866533281792, coefficient := 463914195160612167866533281792 }, { argument := 463827010830605428476598026240, coefficient := 463827010830605428476598026240 }, { argument := 11497961244093217730564456448, coefficient := 11497961244093217730564456448 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 1077294576271120684019613696, coefficient := 1077294576271120684019613696 }, { argument := 37072720844909937746440617984, coefficient := 37072720844909937746440617984 }, { argument := 398937719123397926999145054208, coefficient := 398937719123397926999145054208 }, { argument := 37142375750532265013342633984, coefficient := 37142375750532265013342633984 }, { argument := 1138864790474775118315782144, coefficient := 1138864790474775118315782144 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk8
