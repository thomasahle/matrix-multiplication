import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 5, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk5

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
def constantNumerator : ℤ := (-85540859254461869603251734708224)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1056278760311, 12659518147991, 6330448782747, 1051836535125, 65808652589, 2658838063749,
    892915224265, 1330665168099, 8500006189, 65808652589, 300346852253, 2403174341343,
    16578431939, 3635613254513, 87204950368347, 87214512247423, 3620176615131, 300346852253,
    48313410657873, 1034215434466651, 24179362725267, 2482460949199, 2658838063749, 48313410657873,
    96637363315055, 1336941353909, 1056278760311, 3635613254513, 132125699619, 132125699619,
    25337593267319, 25340355270421, 65784843645, 2403174341343, 96637363315055, 258583088515239,
    48364017430153, 620724416769, 892915224265, 1034215434466651, 258583088515239, 28733603532521,
    12659518147991, 87204950368347, 25337593267319, 16578431939, 1336941353909, 28733603532521,
    669104266423, 68542388165, 1330665168099, 24179362725267, 48364017430153, 669104266423,
    6330448782747, 87214512247423, 25340355270421, 8500006189, 2482460949199, 620724416769,
    68542388165, 1051836535125, 3620176615131, 65784843645
  ]
def negativeCoefficients : Array ℕ := #[
    297316039458499316223574016, 14253350303495574808778768384, 14254903389533699593790816256, 296065664227726476705792000, 18523488954848426678288384, 748396382071155468055609344,
    8042665342546593736168570880, 749097894400694352649125888, 19140312352713654897999872, 18523488954848426678288384, 676320985944256108501663744, 676433441761166997489451008,
    18665654975716882368167936, 1023334156142998939687190528, 49092022747968768387280011264, 49097405607349222805105278976, 1018989128432459694458535936, 676320985944256108501663744,
    27198032279474324101058789376, 291105765330301566821708333056, 27223542239892130461917380608, 698750637860901512537964544, 748396382071155468055609344, 27198032279474324101058789376,
    27200999588484308627703726080, 752631072910097351975108608, 297316039458499316223574016, 1023334156142998939687190528, 297520625785097242659520512, 297520625785097242659520512,
    14263796949645379580647702528, 14265351819162999999904612352, 296268597326248341846097920, 676433441761166997489451008, 27200999588484308627703726080, 291138675270385586044598747136,
    27226521359572153044341620736, 698873563015159214669561856, 8042665342546593736168570880, 291105765330301566821708333056, 291138675270385586044598747136, 8087790385129571446503243776,
    14253350303495574808778768384, 49092022747968768387280011264, 14263796949645379580647702528, 18665654975716882368167936, 752631072910097351975108608, 8087790385129571446503243776,
    753344431233657969628413952, 19292967112436118443786240, 749097894400694352649125888, 27223542239892130461917380608, 27226521359572153044341620736, 753344431233657969628413952,
    14254903389533699593790816256, 49097405607349222805105278976, 14265351819162999999904612352, 19140312352713654897999872, 698750637860901512537964544, 698873563015159214669561856,
    19292967112436118443786240, 296065664227726476705792000, 1018989128432459694458535936, 296268597326248341846097920
  ]
def negativeScales : Array ℕ := #[
    39, 43, 42, 39, 35, 41,
    39, 40, 32, 35, 38, 41,
    33, 41, 46, 46, 41, 38,
    45, 49, 44, 41, 41, 45,
    46, 40, 39, 41, 36, 36,
    44, 44, 35, 41, 46, 47,
    45, 39, 39, 49, 47, 44,
    43, 46, 44, 33, 40, 44,
    39, 35, 40, 44, 45, 39,
    42, 46, 44, 32, 41, 39,
    35, 39, 41, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    39942127771335129, 43525287726870237, 42525444918506853, 39936047661110162, 35937558240761749, 41273933051330746,
    39699732252395214, 40275284733869882, 32984816764234953, 35937558240761749, 38127838587722643, 41128078453061728,
    33948588515897015, 41725335876959357, 46309475268413480, 46309633448874897, 41719197221583097, 38127838587722643,
    45457488936140457, 49877458166855508, 44458841454747597, 41174908162005195, 41273933051330746, 45457488936140457,
    46457646325779601, 40282073320399482, 39942127771335129, 41725335876959357, 36943120163882344, 36943120163882344,
    44526344727778142, 44526501984663915, 35937036192913794, 41128078453061728, 46457646325779601, 47877621256467486,
    45458999322742922, 39175161940539931, 39699732252395214, 49877458166855508, 47877621256467486, 44707804168800331,
    43525287726870237, 46309475268413480, 44526344727778142, 33948588515897015, 40282073320399482, 44707804168800331,
    39283440087109723, 35996277430530163, 40275284733869882, 44458841454747597, 45458999322742922, 39283440087109723,
    42525444918506853, 46309633448874897, 44526501984663915, 32984816764234953, 41174908162005195, 39175161940539931,
    35996277430530163, 39936047661110162, 41719197221583097, 35937036192913794
  ]

abbrev PositiveTerm := Fin 0
abbrev NegativeTerm := Fin 64
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
noncomputable def positiveFloor : ℝ := 0 / 1
noncomputable def negativeCeiling : ℝ := 199793447 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 297316039458499316223574016, coefficient := (-297316039458499316223574016) }, { argument := 14253350303495574808778768384, coefficient := (-14253350303495574808778768384) }, { argument := 14254903389533699593790816256, coefficient := (-14254903389533699593790816256) }, { argument := 296065664227726476705792000, coefficient := (-296065664227726476705792000) }, { argument := 18523488954848426678288384, coefficient := (-18523488954848426678288384) }, { argument := 748396382071155468055609344, coefficient := (-748396382071155468055609344) }, { argument := 8042665342546593736168570880, coefficient := (-8042665342546593736168570880) }, { argument := 749097894400694352649125888, coefficient := (-749097894400694352649125888) }, { argument := 19140312352713654897999872, coefficient := (-19140312352713654897999872) }, { argument := 18523488954848426678288384, coefficient := (-18523488954848426678288384) }, { argument := 676320985944256108501663744, coefficient := (-676320985944256108501663744) }, { argument := 676433441761166997489451008, coefficient := (-676433441761166997489451008) }, { argument := 18665654975716882368167936, coefficient := (-18665654975716882368167936) }, { argument := 1023334156142998939687190528, coefficient := (-1023334156142998939687190528) }, { argument := 49092022747968768387280011264, coefficient := (-49092022747968768387280011264) }, { argument := 49097405607349222805105278976, coefficient := (-49097405607349222805105278976) }, { argument := 1018989128432459694458535936, coefficient := (-1018989128432459694458535936) }, { argument := 676320985944256108501663744, coefficient := (-676320985944256108501663744) }, { argument := 27198032279474324101058789376, coefficient := (-27198032279474324101058789376) }, { argument := 291105765330301566821708333056, coefficient := (-291105765330301566821708333056) }, { argument := 27223542239892130461917380608, coefficient := (-27223542239892130461917380608) }, { argument := 698750637860901512537964544, coefficient := (-698750637860901512537964544) }, { argument := 748396382071155468055609344, coefficient := (-748396382071155468055609344) }, { argument := 27198032279474324101058789376, coefficient := (-27198032279474324101058789376) }, { argument := 27200999588484308627703726080, coefficient := (-27200999588484308627703726080) }, { argument := 752631072910097351975108608, coefficient := (-752631072910097351975108608) }, { argument := 297316039458499316223574016, coefficient := (-297316039458499316223574016) }, { argument := 1023334156142998939687190528, coefficient := (-1023334156142998939687190528) }, { argument := 297520625785097242659520512, coefficient := (-297520625785097242659520512) }, { argument := 297520625785097242659520512, coefficient := (-297520625785097242659520512) }, { argument := 14263796949645379580647702528, coefficient := (-14263796949645379580647702528) }, { argument := 14265351819162999999904612352, coefficient := (-14265351819162999999904612352) }, { argument := 296268597326248341846097920, coefficient := (-296268597326248341846097920) }, { argument := 676433441761166997489451008, coefficient := (-676433441761166997489451008) }, { argument := 27200999588484308627703726080, coefficient := (-27200999588484308627703726080) }, { argument := 291138675270385586044598747136, coefficient := (-291138675270385586044598747136) }, { argument := 27226521359572153044341620736, coefficient := (-27226521359572153044341620736) }, { argument := 698873563015159214669561856, coefficient := (-698873563015159214669561856) }, { argument := 8042665342546593736168570880, coefficient := (-8042665342546593736168570880) }, { argument := 291105765330301566821708333056, coefficient := (-291105765330301566821708333056) }, { argument := 291138675270385586044598747136, coefficient := (-291138675270385586044598747136) }, { argument := 8087790385129571446503243776, coefficient := (-8087790385129571446503243776) }, { argument := 14253350303495574808778768384, coefficient := (-14253350303495574808778768384) }, { argument := 49092022747968768387280011264, coefficient := (-49092022747968768387280011264) }, { argument := 14263796949645379580647702528, coefficient := (-14263796949645379580647702528) }, { argument := 18665654975716882368167936, coefficient := (-18665654975716882368167936) }, { argument := 752631072910097351975108608, coefficient := (-752631072910097351975108608) }, { argument := 8087790385129571446503243776, coefficient := (-8087790385129571446503243776) }, { argument := 753344431233657969628413952, coefficient := (-753344431233657969628413952) }, { argument := 19292967112436118443786240, coefficient := (-19292967112436118443786240) }, { argument := 749097894400694352649125888, coefficient := (-749097894400694352649125888) }, { argument := 27223542239892130461917380608, coefficient := (-27223542239892130461917380608) }, { argument := 27226521359572153044341620736, coefficient := (-27226521359572153044341620736) }, { argument := 753344431233657969628413952, coefficient := (-753344431233657969628413952) }, { argument := 14254903389533699593790816256, coefficient := (-14254903389533699593790816256) }, { argument := 49097405607349222805105278976, coefficient := (-49097405607349222805105278976) }, { argument := 14265351819162999999904612352, coefficient := (-14265351819162999999904612352) }, { argument := 19140312352713654897999872, coefficient := (-19140312352713654897999872) }, { argument := 698750637860901512537964544, coefficient := (-698750637860901512537964544) }, { argument := 698873563015159214669561856, coefficient := (-698873563015159214669561856) }, { argument := 19292967112436118443786240, coefficient := (-19292967112436118443786240) }, { argument := 296065664227726476705792000, coefficient := (-296065664227726476705792000) }, { argument := 1018989128432459694458535936, coefficient := (-1018989128432459694458535936) }, { argument := 296268597326248341846097920, coefficient := (-296268597326248341846097920) }] }

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

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 85173549682879498943494025641984
def positiveArguments : Array ℕ := #[
    11, 6162511, 21224899, 3083511, 2028183, 73459443,
    73467721, 2039597, 73583, 5918649, 126710813, 2962101,
    304097, 342661, 16434381, 16436179, 341211
  ]
def positiveCoefficients : Array ℕ := #[
    1743019575313815427057966907392, 58203270793431000390997901312, 200463503279786899653062033408, 58245875983839450330115866624, 19155646840652011276899188736, 693804822946946358011448262656,
    693883006446436747857606213632, 19263449022722959537837441024, 2779887143271976830075142144, 111800118645879771097586466816, 1196749792656726636097957789696, 111905011850197271657073082368,
    2872114960682421001098625024, 3236341642773190997140570112, 155218340002219445553412964352, 155235321632091844797601415168, 3222646779972869026020851712
  ]
def positiveScales : Array ℕ := #[
    3, 22, 24, 21, 20, 26,
    26, 20, 16, 22, 26, 21,
    18, 18, 23, 23, 18
  ]
def negativeArguments : Array ℕ := #[
    1, 9, 9, 1
  ]
def negativeCoefficients : Array ℕ := #[
    316912650057057350374175801344, 1426106925256758076683791106048, 1426106925256758076683791106048, 316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    0, 3, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3459431618637292, 22555086886008344, 24339254352852237, 21556142562264666, 20951756399149243, 26130444621209716,
    26130607186513993, 20959852689616238, 16167084876149720, 22496836470949761, 26916964402359341, 21498189402967426,
    18214172058294928, 18386422475140169, 23970213781727482, 23970371610839463, 18380304631613657
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 3169925001442313, 3169925001442313, 0
  ]

abbrev PositiveTerm := Fin 17
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 143443979 / 125000000000
noncomputable def negativeCeiling : ℝ := 108830739 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1743019575313815427057966907392, coefficient := 1743019575313815427057966907392 }, { argument := 58203270793431000390997901312, coefficient := 58203270793431000390997901312 }, { argument := 200463503279786899653062033408, coefficient := 200463503279786899653062033408 }, { argument := 58245875983839450330115866624, coefficient := 58245875983839450330115866624 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 19155646840652011276899188736, coefficient := 19155646840652011276899188736 }, { argument := 693804822946946358011448262656, coefficient := 693804822946946358011448262656 }, { argument := 693883006446436747857606213632, coefficient := 693883006446436747857606213632 }, { argument := 19263449022722959537837441024, coefficient := 19263449022722959537837441024 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 2779887143271976830075142144, coefficient := 2779887143271976830075142144 }, { argument := 111800118645879771097586466816, coefficient := 111800118645879771097586466816 }, { argument := 1196749792656726636097957789696, coefficient := 1196749792656726636097957789696 }, { argument := 111905011850197271657073082368, coefficient := 111905011850197271657073082368 }, { argument := 2872114960682421001098625024, coefficient := 2872114960682421001098625024 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 3236341642773190997140570112, coefficient := 3236341642773190997140570112 }, { argument := 155218340002219445553412964352, coefficient := 155218340002219445553412964352 }, { argument := 155235321632091844797601415168, coefficient := 155235321632091844797601415168 }, { argument := 3222646779972869026020851712, coefficient := 3222646779972869026020851712 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

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

end TermShard1


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk5
