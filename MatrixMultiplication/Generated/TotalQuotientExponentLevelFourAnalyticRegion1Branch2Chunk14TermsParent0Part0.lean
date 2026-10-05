import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 14, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-233493000140197204034222741782528)
def positiveArguments : Array ℕ := #[
    2239, 289, 2270185155, 509, 2270150973, 257,
    892436613, 285, 93, 12171484389, 939, 3569746183,
    1881, 843, 285, 93
  ]
def positiveCoefficients : Array ℕ := #[
    177391855869437851871944904802304, 91587755866489574258136806588416, 85765170287041842913995695063040, 39381967499766159995228389376, 85763878927592903312294138609664, 39768823762042841331134365696,
    16857650997267634780090077806592, 88203227799083344586562600960, 3597763239173136423925579776, 57478209925384722640469432991744, 72651606055560754883142352896, 16857649726951050888155515322368,
    72767662934243759283914145792, 65223965819848473233747607552, 88203227799083344586562600960, 3597763239173136423925579776
  ]
def positiveScales : Array ℕ := #[
    11, 8, 31, 8, 31, 8,
    29, 8, 6, 33, 9, 31,
    10, 9, 8, 6
  ]
def negativeArguments : Array ℕ := #[
    892443079, 285, 93, 6085716329, 939, 1784886025,
    1881, 843, 285, 93, 4758762304848561, 509,
    4758688632913231, 257, 892430147, 509, 509, 285,
    93, 4758692607016271, 509, 4758618935149233, 257, 1521442015,
    939, 892430079, 257, 257, 1881, 843,
    285, 93, 289, 1083, 289
  ]
def negativeCoefficients : Array ℕ := #[
    8428886568277173860296942419968, 44101613899541672293281300480, 1798881619586568211962789888, 28738982816322098655426441641984, 36325803027780377441571176448, 8428885940202431638634128998400,
    36383831467121879641957072896, 32611982909924236616873803776, 44101613899541672293281300480, 1798881619586568211962789888, 21431560142860742009983919456256, 9845491874941539998807097344,
    21431228353960242158704657432576, 9942205940510710332783591424, 8428764428990460919793135386624, 9845491874941539998807097344, 9845491874941539998807097344, 44101613899541672293281300480,
    1798881619586568211962789888, 21431246251729212234660017340416, 9845491874941539998807097344, 21430914463136272209133141229568, 9942205940510710332783591424, 28739227109062623985042991349760,
    36325803027780377441571176448, 8428763786748619249521386323968, 9942205940510710332783591424, 9942205940510710332783591424, 36383831467121879641957072896, 32611982909924236616873803776,
    44101613899541672293281300480, 1798881619586568211962789888, 91587755866489574258136806588416, 171608200005896555227616196427776, 91587755866489574258136806588416
  ]
def negativeScales : Array ℕ := #[
    29, 8, 6, 32, 9, 30,
    10, 9, 8, 6, 52, 8,
    52, 8, 29, 8, 8, 8,
    6, 52, 8, 52, 8, 30,
    9, 29, 8, 8, 10, 9,
    8, 6, 8, 10, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    11128638812852597, 8174925682500678, 31080162821681672, 8991521844801183, 31080141098971944, 8005624549193878,
    29733174461723324, 8154818109052103, 6539158811107971, 33502786073380282, 9874981347482478, 31733174353008325,
    10877284133344468, 9719388820935039, 8154818109052103, 6539158811107971
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    29733184914655376, 8154818109052105, 6539158811108986, 32502779941653903, 9874981350423323, 30733184807153591,
    10877284136413052, 9719388821055554, 8154818109052105, 6539158811108986, 52079507818514794, 8991521866745102,
    52079485483514288, 8005624549193879, 29733164009044757, 8991521866745102, 8991521866745102, 8154818109052105,
    6539158811108986, 52079486688345450, 8991521866745102, 52079464353038518, 8005624549193879, 30502792205081234,
    9874981350423323, 29733163899116526, 8005624549193879, 8005624549193879, 10877284136413052, 9719388821055554,
    8154818109052105, 6539158811108986, 8174925682500679, 10080817527608328, 8174925682500679
  ]

abbrev PositiveTerm := Fin 16
abbrev NegativeTerm := Fin 35
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
noncomputable def positiveFloor : ℝ := 66325183071 / 500000000000
noncomputable def negativeCeiling : ℝ := 63301855011 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8428886568277173860296942419968, coefficient := (-8428886568277173860296942419968) }, { argument := 44101613899541672293281300480, coefficient := (-44101613899541672293281300480) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 28738982816322098655426441641984, coefficient := (-28738982816322098655426441641984) }, { argument := 36325803027780377441571176448, coefficient := (-36325803027780377441571176448) }, { argument := 8428885940202431638634128998400, coefficient := (-8428885940202431638634128998400) }, { argument := 36383831467121879641957072896, coefficient := (-36383831467121879641957072896) }, { argument := 32611982909924236616873803776, coefficient := (-32611982909924236616873803776) }, { argument := 44101613899541672293281300480, coefficient := (-44101613899541672293281300480) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 21431560142860742009983919456256, coefficient := (-21431560142860742009983919456256) }, { argument := 9845491874941539998807097344, coefficient := (-9845491874941539998807097344) }, { argument := 21431228353960242158704657432576, coefficient := (-21431228353960242158704657432576) }, { argument := 9942205940510710332783591424, coefficient := (-9942205940510710332783591424) }, { argument := 8428764428990460919793135386624, coefficient := (-8428764428990460919793135386624) }, { argument := 9845491874941539998807097344, coefficient := (-9845491874941539998807097344) }, { argument := 9845491874941539998807097344, coefficient := (-9845491874941539998807097344) }, { argument := 44101613899541672293281300480, coefficient := (-44101613899541672293281300480) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 21431246251729212234660017340416, coefficient := (-21431246251729212234660017340416) }, { argument := 9845491874941539998807097344, coefficient := (-9845491874941539998807097344) }, { argument := 21430914463136272209133141229568, coefficient := (-21430914463136272209133141229568) }, { argument := 9942205940510710332783591424, coefficient := (-9942205940510710332783591424) }, { argument := 28739227109062623985042991349760, coefficient := (-28739227109062623985042991349760) }, { argument := 36325803027780377441571176448, coefficient := (-36325803027780377441571176448) }, { argument := 8428763786748619249521386323968, coefficient := (-8428763786748619249521386323968) }, { argument := 9942205940510710332783591424, coefficient := (-9942205940510710332783591424) }, { argument := 9942205940510710332783591424, coefficient := (-9942205940510710332783591424) }, { argument := 36383831467121879641957072896, coefficient := (-36383831467121879641957072896) }, { argument := 32611982909924236616873803776, coefficient := (-32611982909924236616873803776) }, { argument := 44101613899541672293281300480, coefficient := (-44101613899541672293281300480) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 177391855869437851871944904802304, coefficient := 177391855869437851871944904802304 }, { argument := 91587755866489574258136806588416, coefficient := 91587755866489574258136806588416 }, { argument := 91587755866489574258136806588416, coefficient := (-91587755866489574258136806588416) }, { argument := 85765170287041842913995695063040, coefficient := 85765170287041842913995695063040 }, { argument := 39381967499766159995228389376, coefficient := 39381967499766159995228389376 }, { argument := 85763878927592903312294138609664, coefficient := 85763878927592903312294138609664 }, { argument := 39768823762042841331134365696, coefficient := 39768823762042841331134365696 }, { argument := 171608200005896555227616196427776, coefficient := (-171608200005896555227616196427776) }, { argument := 16857650997267634780090077806592, coefficient := 16857650997267634780090077806592 }, { argument := 88203227799083344586562600960, coefficient := 88203227799083344586562600960 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 57478209925384722640469432991744, coefficient := 57478209925384722640469432991744 }, { argument := 72651606055560754883142352896, coefficient := 72651606055560754883142352896 }, { argument := 16857649726951050888155515322368, coefficient := 16857649726951050888155515322368 }, { argument := 72767662934243759283914145792, coefficient := 72767662934243759283914145792 }, { argument := 65223965819848473233747607552, coefficient := 65223965819848473233747607552 }, { argument := 88203227799083344586562600960, coefficient := 88203227799083344586562600960 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 91587755866489574258136806588416, coefficient := (-91587755866489574258136806588416) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk14
