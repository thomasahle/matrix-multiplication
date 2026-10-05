import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 5, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-227315066220433219564959436898304)
def positiveArguments : Array ℕ := #[
    9, 93, 285, 843, 1881, 93,
    939, 1911, 93, 285, 93, 1799,
    7175, 3563, 7175, 9, 5, 5,
    5, 5, 93, 2253, 1707, 951,
    93, 951, 1899, 93, 2253, 93,
    470259, 73616409, 18404109, 1881063, 35215, 4026445,
    2640221, 1006613, 35215, 311003, 58409253, 7301157,
    38875, 355423, 16064473, 44665
  ]
def positiveCoefficients : Array ℕ := #[
    5570730176784211237046059008, 7195526478346272847851159552, 176406455598166689173125201920, 130447931639696946467495215104, 145535325868487518567828291584, 7195526478346272847851159552,
    145303212111121509766284705792, 147856463442147606583264149504, 7195526478346272847851159552, 176406455598166689173125201920, 7195526478346272847851159552, 278381766334299889317940559872,
    277569368183518858512538009600, 275673772498363119966598725632, 277569368183518858512538009600, 1426106925256758076683791106048, 198070406285660843983859875840, 198070406285660843983859875840,
    198070406285660843983859875840, 198070406285660843983859875840, 3597763239173136423925579776, 87158715890936304979616464896, 66036363970629504039150157824, 73580061085024790089316696064,
    3597763239173136423925579776, 73580061085024790089316696064, 73464004206341785688544903168, 3597763239173136423925579776, 87158715890936304979616464896, 3597763239173136423925579776,
    17765882718942371908379738112, 695287324901646591472674275328, 695287579909436666433515814912, 17766137726732446869221277696, 665192542777018224801218560, 152114791304944548979681525760,
    1595915668194377927135957352448, 152115055757467589679813492736, 665192542777018224801218560, 5874680573087633081580388352, 1103319594626613093228034916352, 1103319651295010887663777480704,
    5874623904689838645837824000, 26855002599055646572599574528, 1213797261762630048879977955328, 26998335866543706044125675520
  ]
def positiveScales : Array ℕ := #[
    3, 6, 8, 9, 10, 6,
    9, 10, 6, 8, 6, 10,
    12, 11, 12, 3, 2, 2,
    2, 2, 6, 11, 10, 9,
    6, 9, 10, 6, 11, 6,
    18, 26, 24, 20, 15, 21,
    21, 19, 15, 18, 25, 22,
    15, 18, 23, 15
  ]
def negativeArguments : Array ℕ := #[
    3, 3, 7, 9, 5, 3,
    9, 3, 7, 1
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 950737950171172051122527404032, 1109194275199700726309615304704, 1426106925256758076683791106048, 792281625142643375935439503360, 475368975085586025561263702016,
    1426106925256758076683791106048, 1901475900342344102245054808064, 2218388550399401452619230609408, 1267650600228229401496703205376
  ]
def negativeScales : Array ℕ := #[
    1, 1, 2, 3, 2, 1,
    3, 1, 2, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3169925001442312, 6539158811107971, 8154818109052103, 9719388820935039, 10877284133344468, 6539158811107971,
    9874981347482478, 10900112062706946, 6539158811107971, 8154818109052103, 6539158811107971, 10812979471199464,
    12808763116402615, 11798876768094178, 12808763116402615, 3169925001442312, 2321928094887362, 2321928094887362,
    2321928094887362, 2321928094887362, 6539158811107971, 11137631598235427, 10737247343017206, 9893301530621223,
    6539158811107971, 9893301530621223, 10891024189919810, 6539158811107971, 11137631598235427, 6539158811107971,
    18843096029215483, 26133524041151016, 24133524570282490, 20843116737211756, 15103902462276700, 21941075195529824,
    21332227264915318, 19941077703662038, 15103902462276700, 18246568971397987, 25799693598341862, 22799693672441166,
    15246555054792689, 18439177517965153, 23937370317221351, 15446857141489837
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 1584962500724866, 2807354922807594, 3169925001442313, 2321928094887363, 1584962500724866,
    3169925001442313, 1584962500724866, 2807354922807594, 0
  ]

abbrev PositiveTerm := Fin 46
abbrev NegativeTerm := Fin 10
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
noncomputable def positiveFloor : ℝ := 582563843 / 250000000000
noncomputable def negativeCeiling : ℝ := 78993723 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 130447931639696946467495215104, coefficient := 130447931639696946467495215104 }, { argument := 145535325868487518567828291584, coefficient := 145535325868487518567828291584 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 145303212111121509766284705792, coefficient := 145303212111121509766284705792 }, { argument := 147856463442147606583264149504, coefficient := 147856463442147606583264149504 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 278381766334299889317940559872, coefficient := 278381766334299889317940559872 }, { argument := 277569368183518858512538009600, coefficient := 277569368183518858512538009600 }, { argument := 275673772498363119966598725632, coefficient := 275673772498363119966598725632 }, { argument := 277569368183518858512538009600, coefficient := 277569368183518858512538009600 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 1426106925256758076683791106048, coefficient := 1426106925256758076683791106048 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 198070406285660843983859875840, coefficient := 198070406285660843983859875840 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 87158715890936304979616464896, coefficient := 87158715890936304979616464896 }, { argument := 66036363970629504039150157824, coefficient := 66036363970629504039150157824 }, { argument := 73580061085024790089316696064, coefficient := 73580061085024790089316696064 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 73580061085024790089316696064, coefficient := 73580061085024790089316696064 }, { argument := 73464004206341785688544903168, coefficient := 73464004206341785688544903168 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 87158715890936304979616464896, coefficient := 87158715890936304979616464896 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 17765882718942371908379738112, coefficient := 17765882718942371908379738112 }, { argument := 695287324901646591472674275328, coefficient := 695287324901646591472674275328 }, { argument := 695287579909436666433515814912, coefficient := 695287579909436666433515814912 }, { argument := 17766137726732446869221277696, coefficient := 17766137726732446869221277696 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 665192542777018224801218560, coefficient := 665192542777018224801218560 }, { argument := 152114791304944548979681525760, coefficient := 152114791304944548979681525760 }, { argument := 1595915668194377927135957352448, coefficient := 1595915668194377927135957352448 }, { argument := 152115055757467589679813492736, coefficient := 152115055757467589679813492736 }, { argument := 665192542777018224801218560, coefficient := 665192542777018224801218560 }, { argument := 1901475900342344102245054808064, coefficient := (-1901475900342344102245054808064) }, { argument := 5874680573087633081580388352, coefficient := 5874680573087633081580388352 }, { argument := 1103319594626613093228034916352, coefficient := 1103319594626613093228034916352 }, { argument := 1103319651295010887663777480704, coefficient := 1103319651295010887663777480704 }, { argument := 5874623904689838645837824000, coefficient := 5874623904689838645837824000 }, { argument := 2218388550399401452619230609408, coefficient := (-2218388550399401452619230609408) }, { argument := 26855002599055646572599574528, coefficient := 26855002599055646572599574528 }, { argument := 1213797261762630048879977955328, coefficient := 1213797261762630048879977955328 }, { argument := 26998335866543706044125675520, coefficient := 26998335866543706044125675520 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }] }

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

end TermShard6


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk5
