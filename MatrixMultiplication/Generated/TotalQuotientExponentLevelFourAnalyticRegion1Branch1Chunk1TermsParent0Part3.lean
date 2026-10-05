import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 1, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-759704536667576495975064418648064)
def positiveArguments : Array ℕ := #[
    377, 15631, 23403, 725, 23403, 24389,
    14529, 725, 3689, 4165, 1785, 47005,
    4165, 1785, 4165, 4165, 172669, 1071,
    47005, 172669, 3689, 4165, 1071, 4165,
    747, 21663, 19173, 1245, 747, 1245,
    38097, 1245, 747, 610299, 39093, 21663,
    38097, 1245, 39093, 1245, 38097, 1245,
    747, 329, 245, 259, 21, 4501,
    8141, 245, 4501, 133, 133, 259,
    259, 8141, 259, 329, 21, 7
  ]
def positiveCoefficients : Array ℕ := #[
    29168962175661772727310614528, 604695023564680596154631585792, 905359710606117330420756381696, 28047079015059396853183283200, 905359710606117330420756381696, 943503738066598110141085646848,
    562063463461790312937792995328, 28047079015059396853183283200, 285422550307735489631429328896, 322251266476475552809678274560, 276215371265550473836867092480, 3636835721663081238852083384320,
    322251266476475552809678274560, 276215371265550473836867092480, 322251266476475552809678274560, 322251266476475552809678274560, 13359616790210457917909805039616, 331458445518660568604240510976,
    3636835721663081238852083384320, 13359616790210457917909805039616, 285422550307735489631429328896, 322251266476475552809678274560, 331458445518660568604240510976, 322251266476475552809678274560,
    28898162792068095792176431104, 419023360484987388986558251008, 741719511663081125332528398336, 24081802326723413160147025920, 462370604673089532674822897664, 24081802326723413160147025920,
    736903151197736442700498993152, 770617674455149221124704829440, 462370604673089532674822897664, 11804899500559817131104072105984, 756168593059115173228616613888, 419023360484987388986558251008,
    736903151197736442700498993152, 24081802326723413160147025920, 756168593059115173228616613888, 24081802326723413160147025920, 736903151197736442700498993152, 770617674455149221124704829440,
    28898162792068095792176431104, 6363785514451407975653310464, 4738989212889346364848209920, 5009788596483023299982393344, 6499185206248246443220402176, 87062001825367134645639970816,
    157469841559723137780527661056, 4738989212889346364848209920, 87062001825367134645639970816, 5145188288279861767549485056, 5145188288279861767549485056, 5009788596483023299982393344,
    5009788596483023299982393344, 157469841559723137780527661056, 5009788596483023299982393344, 6363785514451407975653310464, 6499185206248246443220402176, 277298568799925181577403826176
  ]
def positiveScales : Array ℕ := #[
    8, 13, 14, 9, 14, 14,
    13, 9, 11, 12, 10, 15,
    12, 10, 12, 12, 17, 10,
    15, 17, 11, 12, 10, 12,
    9, 14, 14, 10, 9, 10,
    15, 10, 9, 19, 15, 14,
    15, 10, 15, 10, 15, 10,
    9, 8, 7, 8, 4, 12,
    12, 7, 12, 7, 7, 8,
    8, 12, 8, 8, 4, 2
  ]
def negativeArguments : Array ℕ := #[
    29, 119, 249, 7
  ]
def negativeCoefficients : Array ℕ := #[
    4595233425827331580425549119488, 37712605356789824694526920359936, 19727812466051820060792443633664, 554597137599850363154807652352
  ]
def negativeScales : Array ℕ := #[
    4, 6, 7, 2
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8558420713268557, 13932122457405559, 14514405858405324, 9501837184902278, 14514405858405324, 14573942985382547,
    13826647788254566, 9501837184902278, 11849014073589620, 12024100780252909, 10801708358875019, 15520526606372375,
    12024100780252909, 10801708358875019, 12024100780252909, 12024100780252909, 17397649567374687, 10064742764750255,
    15520526606372375, 17397649567374687, 11849014073589620, 12024100780252909, 10064742764750255, 12024100780252909,
    9544964432789165, 14402945427916808, 14226788472762982, 10281930026955443, 9544964432789165, 10281930026955443,
    15217389774760732, 10281930026955443, 9544964432789165, 19219156700934920, 15254622680959707, 14402945427916808,
    15217389774760732, 10281930026955443, 15254622680959707, 10281930026955443, 15217389774760732, 10281930026955443,
    9544964432789165, 8361943773735241, 7936637938489789, 8016808287686553, 4392317422778759, 12136029849385551,
    12990990302267154, 7936637938489789, 12136029849385551, 7055282435501189, 7055282435501189, 8016808287686553,
    8016808287686553, 12990990302267154, 8016808287686553, 8361943773735241, 4392317422778759, 2807354922011143
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    4857980997143165, 6894817767286876, 7960001944397948, 2807354922807594
  ]

abbrev PositiveTerm := Fin 60
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
noncomputable def positiveFloor : ℝ := 1530648887 / 125000000000
noncomputable def negativeCeiling : ℝ := 1061513543 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 29168962175661772727310614528, coefficient := 29168962175661772727310614528 }, { argument := 604695023564680596154631585792, coefficient := 604695023564680596154631585792 }, { argument := 905359710606117330420756381696, coefficient := 905359710606117330420756381696 }, { argument := 28047079015059396853183283200, coefficient := 28047079015059396853183283200 }, { argument := 905359710606117330420756381696, coefficient := 905359710606117330420756381696 }, { argument := 943503738066598110141085646848, coefficient := 943503738066598110141085646848 }, { argument := 562063463461790312937792995328, coefficient := 562063463461790312937792995328 }, { argument := 28047079015059396853183283200, coefficient := 28047079015059396853183283200 }, { argument := 4595233425827331580425549119488, coefficient := (-4595233425827331580425549119488) }, { argument := 285422550307735489631429328896, coefficient := 285422550307735489631429328896 }, { argument := 322251266476475552809678274560, coefficient := 322251266476475552809678274560 }, { argument := 276215371265550473836867092480, coefficient := 276215371265550473836867092480 }, { argument := 3636835721663081238852083384320, coefficient := 3636835721663081238852083384320 }, { argument := 322251266476475552809678274560, coefficient := 322251266476475552809678274560 }, { argument := 276215371265550473836867092480, coefficient := 276215371265550473836867092480 }, { argument := 322251266476475552809678274560, coefficient := 322251266476475552809678274560 }, { argument := 322251266476475552809678274560, coefficient := 322251266476475552809678274560 }, { argument := 13359616790210457917909805039616, coefficient := 13359616790210457917909805039616 }, { argument := 331458445518660568604240510976, coefficient := 331458445518660568604240510976 }, { argument := 3636835721663081238852083384320, coefficient := 3636835721663081238852083384320 }, { argument := 13359616790210457917909805039616, coefficient := 13359616790210457917909805039616 }, { argument := 285422550307735489631429328896, coefficient := 285422550307735489631429328896 }, { argument := 322251266476475552809678274560, coefficient := 322251266476475552809678274560 }, { argument := 331458445518660568604240510976, coefficient := 331458445518660568604240510976 }, { argument := 322251266476475552809678274560, coefficient := 322251266476475552809678274560 }, { argument := 37712605356789824694526920359936, coefficient := (-37712605356789824694526920359936) }, { argument := 28898162792068095792176431104, coefficient := 28898162792068095792176431104 }, { argument := 419023360484987388986558251008, coefficient := 419023360484987388986558251008 }, { argument := 741719511663081125332528398336, coefficient := 741719511663081125332528398336 }, { argument := 24081802326723413160147025920, coefficient := 24081802326723413160147025920 }, { argument := 462370604673089532674822897664, coefficient := 462370604673089532674822897664 }, { argument := 24081802326723413160147025920, coefficient := 24081802326723413160147025920 }, { argument := 736903151197736442700498993152, coefficient := 736903151197736442700498993152 }, { argument := 770617674455149221124704829440, coefficient := 770617674455149221124704829440 }, { argument := 462370604673089532674822897664, coefficient := 462370604673089532674822897664 }, { argument := 11804899500559817131104072105984, coefficient := 11804899500559817131104072105984 }, { argument := 756168593059115173228616613888, coefficient := 756168593059115173228616613888 }, { argument := 419023360484987388986558251008, coefficient := 419023360484987388986558251008 }, { argument := 736903151197736442700498993152, coefficient := 736903151197736442700498993152 }, { argument := 24081802326723413160147025920, coefficient := 24081802326723413160147025920 }, { argument := 756168593059115173228616613888, coefficient := 756168593059115173228616613888 }, { argument := 24081802326723413160147025920, coefficient := 24081802326723413160147025920 }, { argument := 736903151197736442700498993152, coefficient := 736903151197736442700498993152 }, { argument := 770617674455149221124704829440, coefficient := 770617674455149221124704829440 }, { argument := 28898162792068095792176431104, coefficient := 28898162792068095792176431104 }, { argument := 19727812466051820060792443633664, coefficient := (-19727812466051820060792443633664) }, { argument := 6363785514451407975653310464, coefficient := 6363785514451407975653310464 }, { argument := 4738989212889346364848209920, coefficient := 4738989212889346364848209920 }, { argument := 5009788596483023299982393344, coefficient := 5009788596483023299982393344 }, { argument := 6499185206248246443220402176, coefficient := 6499185206248246443220402176 }, { argument := 87062001825367134645639970816, coefficient := 87062001825367134645639970816 }, { argument := 157469841559723137780527661056, coefficient := 157469841559723137780527661056 }, { argument := 4738989212889346364848209920, coefficient := 4738989212889346364848209920 }, { argument := 87062001825367134645639970816, coefficient := 87062001825367134645639970816 }, { argument := 5145188288279861767549485056, coefficient := 5145188288279861767549485056 }, { argument := 5145188288279861767549485056, coefficient := 5145188288279861767549485056 }, { argument := 5009788596483023299982393344, coefficient := 5009788596483023299982393344 }, { argument := 5009788596483023299982393344, coefficient := 5009788596483023299982393344 }, { argument := 157469841559723137780527661056, coefficient := 157469841559723137780527661056 }, { argument := 5009788596483023299982393344, coefficient := 5009788596483023299982393344 }, { argument := 6363785514451407975653310464, coefficient := 6363785514451407975653310464 }, { argument := 6499185206248246443220402176, coefficient := 6499185206248246443220402176 }, { argument := 554597137599850363154807652352, coefficient := (-554597137599850363154807652352) }, { argument := 277298568799925181577403826176, coefficient := 277298568799925181577403826176 }] }

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


end Parent0

namespace Parent0

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1431211460184254722262503769767936)
def positiveArguments : Array ℕ := #[
    7, 185083443, 1348429371, 370167135, 24359419, 243471263,
    486942407, 24359419, 120611, 4941455, 101748385, 4941455,
    120611, 42083, 8346525, 8346525, 42083
  ]
def positiveCoefficients : Array ℕ := #[
    277298568799925181577403826176, 3496127391029257825357305741312, 12735555332254795940994515730432, 3496129742767766294440622161920, 460136415311112040567061610496, 18396168510930246152647520288768,
    18396164015237354460745276850176, 460136415311112040567061610496, 2278277375461563115476353024, 373365783497737963031106682880, 3843945304080932528132383047680, 373365783497737963031106682880,
    2278277375461563115476353024, 397462697397206559055937536, 78830699816867131034488012800, 78830699816867131034488012800, 397462697397206559055937536
  ]
def positiveScales : Array ℕ := #[
    2, 27, 30, 28, 24, 27,
    28, 24, 16, 22, 26, 22,
    16, 15, 22, 22, 15
  ]
def negativeArguments : Array ℕ := #[
    7, 249, 119, 29, 1
  ]
def negativeCoefficients : Array ℕ := #[
    554597137599850363154807652352, 19727812466051820060792443633664, 37712605356789824694526920359936, 4595233425827331580425549119488, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    2, 7, 6, 4, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 27463600600983902, 30328632811023929, 28463601571440628, 24537976387939518, 27859176259517201,
    28859175906948424, 24537976387939518, 16880001964586045, 22236504471906080, 26600430654612354, 22236504471906080,
    16880001964586045, 15360949934247378, 22992744237616252, 22992744237616252, 15360949934247378
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2807354922807594, 7960001944397948, 6894817767286876, 4857980997143165, 0
  ]

abbrev PositiveTerm := Fin 17
abbrev NegativeTerm := Fin 5
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
noncomputable def positiveFloor : ℝ := 2131896727 / 100000000000
noncomputable def negativeCeiling : ℝ := 1061513543 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 277298568799925181577403826176, coefficient := 277298568799925181577403826176 }, { argument := 554597137599850363154807652352, coefficient := (-554597137599850363154807652352) }, { argument := 3496127391029257825357305741312, coefficient := 3496127391029257825357305741312 }, { argument := 12735555332254795940994515730432, coefficient := 12735555332254795940994515730432 }, { argument := 3496129742767766294440622161920, coefficient := 3496129742767766294440622161920 }, { argument := 19727812466051820060792443633664, coefficient := (-19727812466051820060792443633664) }, { argument := 460136415311112040567061610496, coefficient := 460136415311112040567061610496 }, { argument := 18396168510930246152647520288768, coefficient := 18396168510930246152647520288768 }, { argument := 18396164015237354460745276850176, coefficient := 18396164015237354460745276850176 }, { argument := 460136415311112040567061610496, coefficient := 460136415311112040567061610496 }, { argument := 37712605356789824694526920359936, coefficient := (-37712605356789824694526920359936) }, { argument := 2278277375461563115476353024, coefficient := 2278277375461563115476353024 }, { argument := 373365783497737963031106682880, coefficient := 373365783497737963031106682880 }, { argument := 3843945304080932528132383047680, coefficient := 3843945304080932528132383047680 }, { argument := 373365783497737963031106682880, coefficient := 373365783497737963031106682880 }, { argument := 2278277375461563115476353024, coefficient := 2278277375461563115476353024 }, { argument := 4595233425827331580425549119488, coefficient := (-4595233425827331580425549119488) }, { argument := 397462697397206559055937536, coefficient := 397462697397206559055937536 }, { argument := 78830699816867131034488012800, coefficient := 78830699816867131034488012800 }, { argument := 78830699816867131034488012800, coefficient := 78830699816867131034488012800 }, { argument := 397462697397206559055937536, coefficient := 397462697397206559055937536 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end TermShard7


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1
