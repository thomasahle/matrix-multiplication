import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 18, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-50880127935808813602246089355821056)
def positiveArguments : Array ℕ := #[
    9567, 43583, 1063, 456027, 20197, 1063,
    20197, 39331, 743037, 39331, 456027, 743037,
    9567, 39331, 39331, 43583, 49, 245,
    203, 3647, 1365, 49, 5467, 5467,
    3913, 203, 29360125, 29360131, 161611513, 9340723041,
    2585784591, 411143497, 32115584695, 8028894391, 822289371, 7878113,
    2085563241, 40391250365, 4171130985, 7878113, 12050399, 2127044641,
    1063522441, 6025079, 355423, 16064473, 44665
  ]
def positiveCoefficients : Array ℕ := #[
    740210772240202068122495090688, 843017823940230133139508297728, 657965130880179616108884525056, 8820845035862407978459733164032, 781333592920213294129300373504, 657965130880179616108884525056,
    781333592920213294129300373504, 760772182580207681125897732096, 28744851655327846978756892688384, 760772182580207681125897732096, 8820845035862407978459733164032, 28744851655327846978756892688384,
    740210772240202068122495090688, 760772182580207681125897732096, 760772182580207681125897732096, 843017823940230133139508297728, 7582382740622954183757135872, 151647654812459083675142717440,
    7853182124216631118891319296, 141086478852305683204909563904, 211223519203068009404663070720, 7582382740622954183757135872, 211494318586661686339797254144, 211494318586661686339797254144,
    151376855428865406740008534016, 7853182124216631118891319296, 554597080931452568719065088000, 554597194268248157590550216704, 12211020675792831116137902112768, 44110317414586626847065595969536,
    12211022484459194055212018958336, 7766281079530466113233142939648, 303323121482858715010110523965440, 303323054132467936323230486233088, 7766303529660725675526488850432, 297626694235677034107249885184,
    39395175788813553009583869394944, 381484573849744646970238125998080, 39395218318446097733608663941120, 297626694235677034107249885184, 56906400342805889813477064704, 10044684320225897153363376603136,
    10044685458316219524947873103872, 56905262252483518228980563968, 3356875324881955821574946816, 151724657720328756109997244416, 3374791983317963255515709440
  ]
def positiveScales : Array ℕ := #[
    13, 15, 10, 18, 14, 10,
    14, 15, 19, 15, 18, 19,
    13, 15, 15, 15, 5, 7,
    7, 11, 10, 5, 12, 12,
    11, 7, 24, 24, 27, 33,
    31, 28, 34, 32, 29, 22,
    30, 35, 31, 22, 23, 30,
    29, 22, 18, 23, 15
  ]
def negativeArguments : Array ℕ := #[
    3099, 1063, 7, 7, 865, 7853,
    5817, 255, 1
  ]
def negativeCoefficients : Array ℕ := #[
    245528075631705182202392702091264, 84219536752662990861937219207168, 1109194275199700726309615304704, 1109194275199700726309615304704, 68532360574838652018415517040640, 622178760224517843122100641988608,
    460870221345475651781645159104512, 20203181441137406086353707335680, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    11, 10, 2, 2, 9, 12,
    12, 7, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13223850882973416, 15411477886149187, 10053925881531104, 18798759718991622, 14301853394974689, 10053925881531104,
    14301853394974689, 15263379247160054, 19503074526906521, 15263379247160054, 18798759718991622, 19503074526906521,
    13223850882973416, 15263379247160054, 15263379247160054, 15411477886149187, 5614709844114682, 7936637938489789,
    7665335917183229, 11832494484259625, 10414685235807213, 5614709844114682, 12416533660199582, 12416533660199582,
    11934059394410200, 7665335917183229, 24807354774597435, 24807355069424836, 27267954736621545, 33120887083502688,
    31267954950309972, 28615066769255141, 34902554510920665, 32902554190582127, 29615070939673961, 22909418679454022,
    30957789913307298, 35233323756154125, 31957791470788763, 22909418679454022, 23522577580441948, 30986203164757962,
    29986203328219260, 22522548727207987, 18439177517965153, 23937370317221351, 15446857141489837
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    11597587039591505, 10053925881531105, 2807354922807594, 2807354922807594, 9756556322783439, 12939028190414008,
    12506059588828281, 7994353458490620, 0
  ]

abbrev PositiveTerm := Fin 47
abbrev NegativeTerm := Fin 9
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
noncomputable def positiveFloor : ℝ := 248969451203 / 500000000000
noncomputable def negativeCeiling : ℝ := 44163278531 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 245528075631705182202392702091264, coefficient := (-245528075631705182202392702091264) }, { argument := 740210772240202068122495090688, coefficient := 740210772240202068122495090688 }, { argument := 843017823940230133139508297728, coefficient := 843017823940230133139508297728 }, { argument := 657965130880179616108884525056, coefficient := 657965130880179616108884525056 }, { argument := 8820845035862407978459733164032, coefficient := 8820845035862407978459733164032 }, { argument := 781333592920213294129300373504, coefficient := 781333592920213294129300373504 }, { argument := 657965130880179616108884525056, coefficient := 657965130880179616108884525056 }, { argument := 781333592920213294129300373504, coefficient := 781333592920213294129300373504 }, { argument := 760772182580207681125897732096, coefficient := 760772182580207681125897732096 }, { argument := 28744851655327846978756892688384, coefficient := 28744851655327846978756892688384 }, { argument := 760772182580207681125897732096, coefficient := 760772182580207681125897732096 }, { argument := 8820845035862407978459733164032, coefficient := 8820845035862407978459733164032 }, { argument := 28744851655327846978756892688384, coefficient := 28744851655327846978756892688384 }, { argument := 740210772240202068122495090688, coefficient := 740210772240202068122495090688 }, { argument := 760772182580207681125897732096, coefficient := 760772182580207681125897732096 }, { argument := 760772182580207681125897732096, coefficient := 760772182580207681125897732096 }, { argument := 843017823940230133139508297728, coefficient := 843017823940230133139508297728 }, { argument := 84219536752662990861937219207168, coefficient := (-84219536752662990861937219207168) }, { argument := 7582382740622954183757135872, coefficient := 7582382740622954183757135872 }, { argument := 151647654812459083675142717440, coefficient := 151647654812459083675142717440 }, { argument := 7853182124216631118891319296, coefficient := 7853182124216631118891319296 }, { argument := 141086478852305683204909563904, coefficient := 141086478852305683204909563904 }, { argument := 211223519203068009404663070720, coefficient := 211223519203068009404663070720 }, { argument := 7582382740622954183757135872, coefficient := 7582382740622954183757135872 }, { argument := 211494318586661686339797254144, coefficient := 211494318586661686339797254144 }, { argument := 211494318586661686339797254144, coefficient := 211494318586661686339797254144 }, { argument := 151376855428865406740008534016, coefficient := 151376855428865406740008534016 }, { argument := 7853182124216631118891319296, coefficient := 7853182124216631118891319296 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 554597080931452568719065088000, coefficient := 554597080931452568719065088000 }, { argument := 554597194268248157590550216704, coefficient := 554597194268248157590550216704 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 12211020675792831116137902112768, coefficient := 12211020675792831116137902112768 }, { argument := 44110317414586626847065595969536, coefficient := 44110317414586626847065595969536 }, { argument := 12211022484459194055212018958336, coefficient := 12211022484459194055212018958336 }, { argument := 68532360574838652018415517040640, coefficient := (-68532360574838652018415517040640) }, { argument := 7766281079530466113233142939648, coefficient := 7766281079530466113233142939648 }, { argument := 303323121482858715010110523965440, coefficient := 303323121482858715010110523965440 }, { argument := 303323054132467936323230486233088, coefficient := 303323054132467936323230486233088 }, { argument := 7766303529660725675526488850432, coefficient := 7766303529660725675526488850432 }, { argument := 622178760224517843122100641988608, coefficient := (-622178760224517843122100641988608) }, { argument := 297626694235677034107249885184, coefficient := 297626694235677034107249885184 }, { argument := 39395175788813553009583869394944, coefficient := 39395175788813553009583869394944 }, { argument := 381484573849744646970238125998080, coefficient := 381484573849744646970238125998080 }, { argument := 39395218318446097733608663941120, coefficient := 39395218318446097733608663941120 }, { argument := 297626694235677034107249885184, coefficient := 297626694235677034107249885184 }, { argument := 460870221345475651781645159104512, coefficient := (-460870221345475651781645159104512) }, { argument := 56906400342805889813477064704, coefficient := 56906400342805889813477064704 }, { argument := 10044684320225897153363376603136, coefficient := 10044684320225897153363376603136 }, { argument := 10044685458316219524947873103872, coefficient := 10044685458316219524947873103872 }, { argument := 56905262252483518228980563968, coefficient := 56905262252483518228980563968 }, { argument := 20203181441137406086353707335680, coefficient := (-20203181441137406086353707335680) }, { argument := 3356875324881955821574946816, coefficient := 3356875324881955821574946816 }, { argument := 151724657720328756109997244416, coefficient := 151724657720328756109997244416 }, { argument := 3374791983317963255515709440, coefficient := 3374791983317963255515709440 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18
