import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 0,
parent chunk 10, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk10

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
def constantNumerator : ℤ := 0
def positiveArguments : Array ℕ := #[
    51, 257, 275, 295, 817, 1059,
    1187, 1869, 2207, 4095, 8187, 8291,
    29699, 42007, 132555
  ]
def positiveCoefficients : Array ℕ := #[
    804641218494868612600032359612416, 113850869532997853121922656632832, 5704427701027032306735164424192, 243388915243820045087367015432192, 804561990332354348262438815662080, 1491470159331026155198464865075200,
    244498109519019745813676630736896, 209241577200172115584549572837376, 5942112188569825319515796275200, 1412321224979276081942514458689536, 1410182064591390944827488772030464, 1448449267085780619885170500042752,
    208132382924972414858239957532672, 6656274845473404058584001443528704, 1450509199311151492662602642751488
  ]
def positiveScales : Array ℕ := #[
    5, 8, 8, 8, 9, 10,
    10, 10, 11, 11, 12, 13,
    14, 15, 17
  ]
def negativeArguments : Array ℕ := #[
    3, 5, 9, 29, 31, 37,
    49, 57, 283, 345, 571, 651,
    655, 683, 695, 717, 889, 1361,
    1437, 1783, 2213, 2539, 3463, 8825,
    10155, 18825, 5468919722387
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 396140812571321687967719751680, 2852213850513516153367582212096, 4595233425827331580425549119488, 2456073037942194465399862460416, 2931442013027780490961126162432,
    7764359926397905084167307132928, 4516005263313067242832005169152, 44843139983073615077945875890176, 54667432134842392939545325731840, 45239280795644936765913595641856, 51577533796786083773397111668736,
    51894446446843141123771287470080, 108225669994485085152781036158976, 55063572947413714627513045483520, 113613185045455060109142024781824, 140867672950361992241321143697408, 107829529181913763464813316407296,
    113850869532997853121922656632832, 141263813762933313929288863449088, 701327694576267916378051048374272, 804641218494868612600032359612416, 1097468507147589604345770800054272, 699188534188382779263025361715200,
    804561990332354348262438815662080, 1491470159331026155198464865075200, 3328137422736702029292000721764352
  ]
def negativeScales : Array ℕ := #[
    1, 2, 3, 4, 4, 5,
    5, 5, 8, 8, 9, 9,
    9, 9, 9, 9, 9, 10,
    10, 10, 11, 11, 11, 13,
    13, 14, 42
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    5672425341969176, 8005624549193878, 8103287808412021, 8204571144249203, 9674192268143262, 10048486873992336,
    10213104219641906, 10868050853594526, 11107870914279613, 11999647735076951, 12999119178556044, 13017330404240013,
    14858126734042040, 15358342136579123, 17016231564401741
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 2321928094887363, 3169925001442313, 4857980997143165, 4954196321574415, 5209453365628950,
    5614709844123661, 5832890015409720, 8144658242831883, 8430452551665554, 9157346935362843, 9346513733165637,
    9355351096424814, 9415741768290103, 9440869167610903, 9485829308702073, 9796039609425563, 10410451351504005,
    10488844346457523, 10800090988272228, 11111787735801012, 11310044679647506, 11757806672463691, 13107380563045906,
    13309902619183516, 14200362244446653, 42314393023755477
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 27
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
noncomputable def positiveFloor : ℝ := 263929334027 / 100000000000
noncomputable def negativeCeiling : ℝ := 2670486292201 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3, coefficient := (-475368975085586025561263702016) }, { argument := 5, coefficient := (-396140812571321687967719751680) }, { argument := 9, coefficient := (-2852213850513516153367582212096) }, { argument := 29, coefficient := (-4595233425827331580425549119488) }, { argument := 31, coefficient := (-2456073037942194465399862460416) }, { argument := 37, coefficient := (-2931442013027780490961126162432) }, { argument := 49, coefficient := (-7764359926397905084167307132928) }, { argument := 51, coefficient := 804641218494868612600032359612416 }, { argument := 57, coefficient := (-4516005263313067242832005169152) }, { argument := 257, coefficient := 113850869532997853121922656632832 }, { argument := 275, coefficient := 5704427701027032306735164424192 }, { argument := 283, coefficient := (-44843139983073615077945875890176) }, { argument := 295, coefficient := 243388915243820045087367015432192 }, { argument := 345, coefficient := (-54667432134842392939545325731840) }, { argument := 571, coefficient := (-45239280795644936765913595641856) }, { argument := 651, coefficient := (-51577533796786083773397111668736) }, { argument := 655, coefficient := (-51894446446843141123771287470080) }, { argument := 683, coefficient := (-108225669994485085152781036158976) }, { argument := 695, coefficient := (-55063572947413714627513045483520) }, { argument := 717, coefficient := (-113613185045455060109142024781824) }, { argument := 817, coefficient := 804561990332354348262438815662080 }, { argument := 889, coefficient := (-140867672950361992241321143697408) }, { argument := 1059, coefficient := 1491470159331026155198464865075200 }, { argument := 1187, coefficient := 244498109519019745813676630736896 }, { argument := 1361, coefficient := (-107829529181913763464813316407296) }, { argument := 1437, coefficient := (-113850869532997853121922656632832) }, { argument := 1783, coefficient := (-141263813762933313929288863449088) }, { argument := 1869, coefficient := 209241577200172115584549572837376 }, { argument := 2207, coefficient := 5942112188569825319515796275200 }, { argument := 2213, coefficient := (-701327694576267916378051048374272) }, { argument := 2539, coefficient := (-804641218494868612600032359612416) }, { argument := 3463, coefficient := (-1097468507147589604345770800054272) }, { argument := 4095, coefficient := 1412321224979276081942514458689536 }, { argument := 8187, coefficient := 1410182064591390944827488772030464 }, { argument := 8291, coefficient := 1448449267085780619885170500042752 }, { argument := 8825, coefficient := (-699188534188382779263025361715200) }, { argument := 10155, coefficient := (-804561990332354348262438815662080) }, { argument := 18825, coefficient := (-1491470159331026155198464865075200) }, { argument := 29699, coefficient := 208132382924972414858239957532672 }, { argument := 42007, coefficient := 6656274845473404058584001443528704 }, { argument := 132555, coefficient := 1450509199311151492662602642751488 }, { argument := 5468919722387, coefficient := (-3328137422736702029292000721764352) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form represented by this small term shard. -/
def form : Form := rawForm

/-- Bounded power normalization preserves this shard's exact evaluation. -/
theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  rfl

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch0.Chunk10
