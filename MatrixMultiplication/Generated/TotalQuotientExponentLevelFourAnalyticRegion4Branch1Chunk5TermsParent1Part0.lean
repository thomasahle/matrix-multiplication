import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 1,
parent chunk 5, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk5

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
def constantNumerator : ℤ := 4042891044394279487917365657600
def positiveArguments : Array ℕ := #[
    33, 25165827, 25165821, 84646317, 141874747, 84589021,
    776521, 110140137, 110140343, 776463, 192117, 7695023,
    84889029, 7695045, 96041
  ]
def positiveCoefficients : Array ℕ := #[
    5229058725941446281173900722176, 475369031753983819997006266368, 475368918417188231125521137664, 799461860598318116872088715264, 2679938199993642994691523739648, 798920715178313118487760863232,
    58672267898310716335750905856, 2080488365549883507911486865408, 2080492256779865392499142950912, 58667885542214613304992595968, 1814493763178935259039268864, 72677437400222051842461270016,
    801754210625898631530301882368, 72677645184347298106850672640, 1814163197525134383874310144
  ]
def positiveScales : Array ℕ := #[
    5, 24, 24, 26, 27, 26,
    19, 26, 26, 19, 17, 22,
    26, 22, 16
  ]
def negativeArguments : Array ℕ := #[
    1611593443251, 64550537565773, 712100877829419, 64550722114647, 805649921087, 9744652567789,
    345287773777551, 690576893733829, 19487797488963, 9744652567789, 65258239396131, 19475339832579,
    1611593443251, 1611594963021, 1611594963021, 64550525430195, 712100697733845, 64550709980073,
    805650680769, 65258239396131, 1157502655366129, 578752383781393, 65253465474743, 345287773777551,
    1157502655366129, 2695737809179, 64550537565773, 64550525430195, 19475339832579, 2695737809179,
    690110220790775, 9736918386179, 690576893733829, 578752383781393, 690110220790775, 712100877829419,
    712100697733845, 19487797488963, 65253465474743, 9736918386179, 64550722114647, 64550709980073,
    805649921087, 805650680769, 3, 27, 27, 3
  ]
def negativeCoefficients : Array ℕ := #[
    453623226906121136982982656, 18169361057986280420789977088, 200438578002673406553687588864, 18169413003876291548578578432, 453540585549810338464006144, 5485751709143685926557319168,
    194379736165020850450870566912, 194380115080646681156411981824, 5485327344347840902204489728, 5485751709143685926557319168, 18368561414204387094152871936, 5481820825807285147165261824,
    453623226906121136982982656, 453623654683346492536651776, 453623654683346492536651776, 18169357642124745500440657920, 200438527310275909211463352320, 18169409588297357504846757888,
    453541013212756853473148928, 18368561414204387094152871936, 651616065923407277079551541248, 651617254984416951880470495232, 18367217674792881291586961408, 194379736165020850450870566912,
    651616065923407277079551541248, 194248380686513626425321324544, 18169361057986280420789977088, 18169357642124745500440657920, 5481820825807285147165261824, 194248380686513626425321324544,
    194248758324869063212688998400, 5481397751966584458704846848, 194380115080646681156411981824, 651617254984416951880470495232, 194248758324869063212688998400, 200438578002673406553687588864,
    200438527310275909211463352320, 5485327344347840902204489728, 18367217674792881291586961408, 5481397751966584458704846848, 18169413003876291548578578432, 18169409588297357504846757888,
    453540585549810338464006144, 453541013212756853473148928, 950737950171172051122527404032, 4278320775770274230051373318144, 4278320775770274230051373318144, 950737950171172051122527404032
  ]
def negativeScales : Array ℕ := #[
    40, 45, 49, 45, 39, 43,
    48, 49, 44, 43, 45, 44,
    40, 40, 40, 45, 49, 45,
    39, 45, 50, 49, 45, 48,
    50, 41, 45, 45, 44, 41,
    49, 43, 49, 49, 49, 49,
    49, 44, 45, 43, 45, 45,
    39, 39, 1, 4, 4, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5044394119358453, 24584962672703565, 24584962328738263, 26334943961376408, 27080042578799925, 26333967089061230,
    19566665415386906, 26714765067220029, 26714767765554247, 19566557653410723, 17551625659918800, 22875494207847210,
    26339074777117800, 22875498332493156, 16551362804853739
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    40551624979673001, 45875494346430273, 49339074959551931, 45875498471064839, 39551362124665737, 43147747887737134,
    48294792579432285, 49294795391758160, 44147636279939247, 43147747887737134, 45891225302709271, 44146713736174334,
    40551624979673001, 40551626340167249, 40551626340167249, 45875494075201847, 49339074594683649, 45875498199859627,
    39551363485044368, 45891225302709271, 50039936926410766, 49039939559020590, 45891119759483291, 48294792579432285,
    50039936926410766, 41293817323672677, 45875494346430273, 45875494075201847, 44146713736174334, 41293817323672677,
    49293820128413963, 43146602388119402, 49294795391758160, 49039939559020590, 49293820128413963, 49339074959551931,
    49339074594683649, 44147636279939247, 45891119759483291, 43146602388119402, 45875498471064839, 45875498199859627,
    39551362124665737, 39551363485044368, 1584962500724866, 4754887502413606, 4754887502413606, 1584962500724866
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
noncomputable def positiveFloor : ℝ := 3639726507 / 1000000000000
noncomputable def negativeCeiling : ℝ := 3582393441 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 453623226906121136982982656, coefficient := (-453623226906121136982982656) }, { argument := 18169361057986280420789977088, coefficient := (-18169361057986280420789977088) }, { argument := 200438578002673406553687588864, coefficient := (-200438578002673406553687588864) }, { argument := 18169413003876291548578578432, coefficient := (-18169413003876291548578578432) }, { argument := 453540585549810338464006144, coefficient := (-453540585549810338464006144) }, { argument := 5485751709143685926557319168, coefficient := (-5485751709143685926557319168) }, { argument := 194379736165020850450870566912, coefficient := (-194379736165020850450870566912) }, { argument := 194380115080646681156411981824, coefficient := (-194380115080646681156411981824) }, { argument := 5485327344347840902204489728, coefficient := (-5485327344347840902204489728) }, { argument := 5485751709143685926557319168, coefficient := (-5485751709143685926557319168) }, { argument := 18368561414204387094152871936, coefficient := (-18368561414204387094152871936) }, { argument := 5481820825807285147165261824, coefficient := (-5481820825807285147165261824) }, { argument := 453623226906121136982982656, coefficient := (-453623226906121136982982656) }, { argument := 453623654683346492536651776, coefficient := (-453623654683346492536651776) }, { argument := 453623654683346492536651776, coefficient := (-453623654683346492536651776) }, { argument := 18169357642124745500440657920, coefficient := (-18169357642124745500440657920) }, { argument := 200438527310275909211463352320, coefficient := (-200438527310275909211463352320) }, { argument := 18169409588297357504846757888, coefficient := (-18169409588297357504846757888) }, { argument := 453541013212756853473148928, coefficient := (-453541013212756853473148928) }, { argument := 18368561414204387094152871936, coefficient := (-18368561414204387094152871936) }, { argument := 651616065923407277079551541248, coefficient := (-651616065923407277079551541248) }, { argument := 651617254984416951880470495232, coefficient := (-651617254984416951880470495232) }, { argument := 18367217674792881291586961408, coefficient := (-18367217674792881291586961408) }, { argument := 194379736165020850450870566912, coefficient := (-194379736165020850450870566912) }, { argument := 651616065923407277079551541248, coefficient := (-651616065923407277079551541248) }, { argument := 194248380686513626425321324544, coefficient := (-194248380686513626425321324544) }, { argument := 18169361057986280420789977088, coefficient := (-18169361057986280420789977088) }, { argument := 18169357642124745500440657920, coefficient := (-18169357642124745500440657920) }, { argument := 5481820825807285147165261824, coefficient := (-5481820825807285147165261824) }, { argument := 194248380686513626425321324544, coefficient := (-194248380686513626425321324544) }, { argument := 194248758324869063212688998400, coefficient := (-194248758324869063212688998400) }, { argument := 5481397751966584458704846848, coefficient := (-5481397751966584458704846848) }, { argument := 194380115080646681156411981824, coefficient := (-194380115080646681156411981824) }, { argument := 651617254984416951880470495232, coefficient := (-651617254984416951880470495232) }, { argument := 194248758324869063212688998400, coefficient := (-194248758324869063212688998400) }, { argument := 200438578002673406553687588864, coefficient := (-200438578002673406553687588864) }, { argument := 200438527310275909211463352320, coefficient := (-200438527310275909211463352320) }, { argument := 5485327344347840902204489728, coefficient := (-5485327344347840902204489728) }, { argument := 18367217674792881291586961408, coefficient := (-18367217674792881291586961408) }, { argument := 5481397751966584458704846848, coefficient := (-5481397751966584458704846848) }, { argument := 18169413003876291548578578432, coefficient := (-18169413003876291548578578432) }, { argument := 18169409588297357504846757888, coefficient := (-18169409588297357504846757888) }, { argument := 453540585549810338464006144, coefficient := (-453540585549810338464006144) }, { argument := 453541013212756853473148928, coefficient := (-453541013212756853473148928) }, { argument := 5229058725941446281173900722176, coefficient := 5229058725941446281173900722176 }, { argument := 475369031753983819997006266368, coefficient := 475369031753983819997006266368 }, { argument := 475368918417188231125521137664, coefficient := 475368918417188231125521137664 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 799461860598318116872088715264, coefficient := 799461860598318116872088715264 }, { argument := 2679938199993642994691523739648, coefficient := 2679938199993642994691523739648 }, { argument := 798920715178313118487760863232, coefficient := 798920715178313118487760863232 }, { argument := 4278320775770274230051373318144, coefficient := (-4278320775770274230051373318144) }, { argument := 58672267898310716335750905856, coefficient := 58672267898310716335750905856 }, { argument := 2080488365549883507911486865408, coefficient := 2080488365549883507911486865408 }, { argument := 2080492256779865392499142950912, coefficient := 2080492256779865392499142950912 }, { argument := 58667885542214613304992595968, coefficient := 58667885542214613304992595968 }, { argument := 4278320775770274230051373318144, coefficient := (-4278320775770274230051373318144) }, { argument := 1814493763178935259039268864, coefficient := 1814493763178935259039268864 }, { argument := 72677437400222051842461270016, coefficient := 72677437400222051842461270016 }, { argument := 801754210625898631530301882368, coefficient := 801754210625898631530301882368 }, { argument := 72677645184347298106850672640, coefficient := 72677645184347298106850672640 }, { argument := 1814163197525134383874310144, coefficient := 1814163197525134383874310144 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch1.Chunk5
