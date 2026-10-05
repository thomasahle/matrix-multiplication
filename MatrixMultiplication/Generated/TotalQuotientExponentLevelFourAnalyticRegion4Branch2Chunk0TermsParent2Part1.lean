import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 4, branch 2,
parent chunk 0, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk0

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 27539426866753217482121812115456
def positiveArguments : Array ℕ := #[
    3, 570413, 24595393, 1537213, 285217, 76081,
    187013, 137, 223541, 61, 19, 17,
    17, 61, 2405, 61, 1496113, 17,
    19, 61, 19, 137, 17, 37019
  ]
def positiveCoefficients : Array ℕ := #[
    475368975085586025561263702016, 5387398465186245870559952896, 232296919072413383602844205056, 232297060743407869692200615936, 5387596804578526395658928128, 1437129457532821910012821504,
    28260605537948830731165761536, 5299930793190534301911875584, 270244486642473820342993289216, 4719646399775512298052911104, 735026898325694538221355008, 5261245166962866168321277952,
    5261245166962866168321277952, 4719646399775512298052911104, 93038931077541861285387304960, 4719646399775512298052911104, 28260775543142214038393454592, 5261245166962866168321277952,
    735026898325694538221355008, 4719646399775512298052911104, 735026898325694538221355008, 5299930793190534301911875584, 5261245166962866168321277952, 1398538278634811169326497792
  ]
def positiveScales : Array ℕ := #[
    1, 19, 24, 20, 18, 16,
    17, 7, 17, 5, 4, 4,
    4, 5, 11, 5, 20, 4,
    4, 5, 4, 7, 4, 15
  ]
def negativeArguments : Array ℕ := #[
    4450275, 154933201, 38733343, 278141, 14287725, 497417119,
    124354417, 892979, 4450275, 154933201, 38733343, 278141,
    32088825, 1117149923, 279287789, 2005543, 3981825, 138624443,
    34656149, 248863, 3686940117, 303163792409, 151582003957, 7374078547,
    3, 3
  ]
def negativeCoefficients : Array ℕ := #[
    5130817748914235926118400, 178625819210475048508850176, 178626016360052336279683072, 5130795843405648396025856, 32945250808817725420339200, 1146965786509366100951564288,
    1146967052417178159269543936, 32945110152394163385008128, 5130817748914235926118400, 178625819210475048508850176, 178626016360052336279683072, 5130795843405648396025856,
    36995896400065806414643200, 1287986170096583244511182848, 1287987591648798424753504256, 36995738449819675276607488, 36725853360649267681689600, 1278584811190768768273874944,
    1278586222366690407054573568, 36725696563324641150500864, 8302251068529266462294016, 341332085631349700968841216, 341332328268409125088526336, 8302474349117492143587328,
    475368975085586025561263702016, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    22, 27, 25, 18, 23, 28,
    26, 19, 22, 27, 25, 18,
    24, 30, 28, 20, 21, 27,
    25, 17, 31, 38, 37, 32,
    1, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 19121647336341003, 24551884771706975, 20551885651563582, 18121700448801941, 16215248588491873,
    17512779035371348, 7098032082960526, 17770179937018065, 5930737337099561, 4247927513443585, 4087462841250339,
    4087462841250339, 5930737337099561, 11231821178657404, 5930737337099561, 20512787714056997, 4087462841250339,
    4247927513443585, 5930737337099561, 4247927513443585, 7098032082960526, 4087462841250339, 15175978303538957
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    22085463057960040, 27207071094869376, 25207072687173119, 18085456898506008, 23768272882412886, 28889880922627531,
    26889882514931380, 19768266722958810, 22085463057960040, 27207071094869376, 25207072687173119, 18085456898506008,
    24935567635629530, 30057175664386318, 28057177256690060, 20935561476174636, 21924998392558141, 27046606422676130,
    25046608014979873, 17924992233103382, 31779776838890843, 38141306502971769, 37141307528516019, 32779815638183472,
    1584962500724866, 1584962500724866
  ]

abbrev PositiveTerm := Fin 24
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 112429749 / 500000000000
noncomputable def negativeCeiling : ℝ := 21212701 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5130817748914235926118400, coefficient := (-5130817748914235926118400) }, { argument := 178625819210475048508850176, coefficient := (-178625819210475048508850176) }, { argument := 178626016360052336279683072, coefficient := (-178626016360052336279683072) }, { argument := 5130795843405648396025856, coefficient := (-5130795843405648396025856) }, { argument := 32945250808817725420339200, coefficient := (-32945250808817725420339200) }, { argument := 1146965786509366100951564288, coefficient := (-1146965786509366100951564288) }, { argument := 1146967052417178159269543936, coefficient := (-1146967052417178159269543936) }, { argument := 32945110152394163385008128, coefficient := (-32945110152394163385008128) }, { argument := 5130817748914235926118400, coefficient := (-5130817748914235926118400) }, { argument := 178625819210475048508850176, coefficient := (-178625819210475048508850176) }, { argument := 178626016360052336279683072, coefficient := (-178626016360052336279683072) }, { argument := 5130795843405648396025856, coefficient := (-5130795843405648396025856) }, { argument := 36995896400065806414643200, coefficient := (-36995896400065806414643200) }, { argument := 1287986170096583244511182848, coefficient := (-1287986170096583244511182848) }, { argument := 1287987591648798424753504256, coefficient := (-1287987591648798424753504256) }, { argument := 36995738449819675276607488, coefficient := (-36995738449819675276607488) }, { argument := 36725853360649267681689600, coefficient := (-36725853360649267681689600) }, { argument := 1278584811190768768273874944, coefficient := (-1278584811190768768273874944) }, { argument := 1278586222366690407054573568, coefficient := (-1278586222366690407054573568) }, { argument := 36725696563324641150500864, coefficient := (-36725696563324641150500864) }, { argument := 8302251068529266462294016, coefficient := (-8302251068529266462294016) }, { argument := 341332085631349700968841216, coefficient := (-341332085631349700968841216) }, { argument := 341332328268409125088526336, coefficient := (-341332328268409125088526336) }, { argument := 8302474349117492143587328, coefficient := (-8302474349117492143587328) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 5387398465186245870559952896, coefficient := 5387398465186245870559952896 }, { argument := 232296919072413383602844205056, coefficient := 232296919072413383602844205056 }, { argument := 232297060743407869692200615936, coefficient := 232297060743407869692200615936 }, { argument := 5387596804578526395658928128, coefficient := 5387596804578526395658928128 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 1437129457532821910012821504, coefficient := 1437129457532821910012821504 }, { argument := 28260605537948830731165761536, coefficient := 28260605537948830731165761536 }, { argument := 5299930793190534301911875584, coefficient := 5299930793190534301911875584 }, { argument := 270244486642473820342993289216, coefficient := 270244486642473820342993289216 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 93038931077541861285387304960, coefficient := 93038931077541861285387304960 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 28260775543142214038393454592, coefficient := 28260775543142214038393454592 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 4719646399775512298052911104, coefficient := 4719646399775512298052911104 }, { argument := 735026898325694538221355008, coefficient := 735026898325694538221355008 }, { argument := 5299930793190534301911875584, coefficient := 5299930793190534301911875584 }, { argument := 5261245166962866168321277952, coefficient := 5261245166962866168321277952 }, { argument := 1398538278634811169326497792, coefficient := 1398538278634811169326497792 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end TermShard2


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk0
