import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 21, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-714730407154095996596780779175936)
def positiveArguments : Array ℕ := #[
    123, 111, 57, 57, 111, 3441,
    111, 9, 147, 723, 10845, 19039,
    723, 6025, 723, 19039, 37837, 6025,
    583943, 37355, 10845, 19039, 723, 37355,
    723, 19039, 19039, 723, 1107, 5043,
    123, 52767, 2337, 123, 2337, 4551,
    85977, 4551, 52767, 85977, 1107, 4551,
    4551, 5043, 105, 525, 435, 7815,
    2925, 105, 11715, 11715, 8385, 435,
    61, 67, 61, 67, 3
  ]
def positiveCoefficients : Array ℕ := #[
    76133312416050886906296139776, 4294104511271162828556337152, 4410161389954167229328130048, 4410161389954167229328130048, 4294104511271162828556337152, 133117239849406047685246451712,
    4294104511271162828556337152, 5570730176784211237046059008, 5686787055467215637817851904, 27969707762604060586002087936, 419545616439060908790031319040, 736535637748573595431388315648,
    27969707762604060586002087936, 466161796043401009766701465600, 27969707762604060586002087936, 736535637748573595431388315648, 731874019788139585333721300992, 466161796043401009766701465600,
    11295100318131606466647176511488, 722550783867271565138387271680, 419545616439060908790031319040, 736535637748573595431388315648, 27969707762604060586002087936, 722550783867271565138387271680,
    27969707762604060586002087936, 736535637748573595431388315648, 736535637748573595431388315648, 27969707762604060586002087936, 342599905872228991078332628992, 390183226132260795394767716352,
    304533249664203547625184559104, 4082648878310728810350130495488, 361633233976241712804906663936, 304533249664203547625184559104, 361633233976241712804906663936, 352116569924235351941619646464,
    13304296344704892486875250425856, 352116569924235351941619646464, 4082648878310728810350130495488, 13304296344704892486875250425856, 342599905872228991078332628992, 352116569924235351941619646464,
    352116569924235351941619646464, 390183226132260795394767716352, 32495926031241232216102010880, 649918520624824644322040217600, 33656494818071276223819939840, 604656337938452928021040988160,
    905243653727434326019984588800, 32495926031241232216102010880, 906404222514264370027702517760, 906404222514264370027702517760, 648757951837994600314322288640, 33656494818071276223819939840,
    37757171198204098384423288832, 41470991316060239209120661504, 37757171198204098384423288832, 41470991316060239209120661504, 237684487542793012780631851008
  ]
def positiveScales : Array ℕ := #[
    6, 6, 5, 5, 6, 11,
    6, 3, 7, 9, 13, 14,
    9, 12, 9, 14, 15, 12,
    19, 15, 13, 14, 9, 15,
    9, 14, 14, 9, 10, 12,
    6, 15, 11, 6, 11, 12,
    16, 12, 15, 16, 10, 12,
    12, 12, 6, 9, 8, 12,
    11, 6, 13, 13, 13, 8,
    5, 6, 5, 6, 1
  ]
def negativeArguments : Array ℕ := #[
    3, 241, 123, 15, 1
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 19093987165937705360044092030976, 38980255957018054096023623565312, 4753689750855860255612637020160, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    1, 7, 6, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6942514504772358, 6794415866314396, 5832890014087662, 5832890014087662, 6794415866314396, 11748612176723449,
    6794415866314396, 3169925001442312, 7199672344836364, 9497851836951101, 13404742432559635, 14216670084407064,
    9497851836951101, 12556745526004584, 9497851836951101, 14216670084407064, 15207510085121588, 12556745526004584,
    19155468025681307, 15189013741504198, 13404742432559635, 14216670084407064, 9497851836951101, 15189013741504198,
    9497851836951101, 14216670084407064, 14216670084407064, 9497851836951101, 10112439506781552, 12300066509957323,
    6942514504772358, 15687348342835456, 11190442018782825, 6942514504772358, 11190442018782825, 12151967870968189,
    16391663150714675, 12151967870968189, 15687348342835456, 16391663150714675, 10112439506781552, 12151967870968189,
    12151967870968189, 12300066509957323, 6714245517659862, 9036173612553484, 8764871590716857, 12932030157413262,
    11514220909358101, 6714245517659862, 13516069333750468, 13516069333750468, 13033595068451708, 8764871590716857,
    5930737337099561, 6066089190457772, 5930737337099561, 6066089190457772, 1584962500720924
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 7912889341723050, 6942514514520450, 3906890600547867, 0
  ]

abbrev PositiveTerm := Fin 59
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
noncomputable def positiveFloor : ℝ := 12016361003 / 1000000000000
noncomputable def negativeCeiling : ℝ := 5308767971 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 76133312416050886906296139776, coefficient := 76133312416050886906296139776 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 133117239849406047685246451712, coefficient := 133117239849406047685246451712 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 5686787055467215637817851904, coefficient := 5686787055467215637817851904 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 27969707762604060586002087936, coefficient := 27969707762604060586002087936 }, { argument := 419545616439060908790031319040, coefficient := 419545616439060908790031319040 }, { argument := 736535637748573595431388315648, coefficient := 736535637748573595431388315648 }, { argument := 27969707762604060586002087936, coefficient := 27969707762604060586002087936 }, { argument := 466161796043401009766701465600, coefficient := 466161796043401009766701465600 }, { argument := 27969707762604060586002087936, coefficient := 27969707762604060586002087936 }, { argument := 736535637748573595431388315648, coefficient := 736535637748573595431388315648 }, { argument := 731874019788139585333721300992, coefficient := 731874019788139585333721300992 }, { argument := 466161796043401009766701465600, coefficient := 466161796043401009766701465600 }, { argument := 11295100318131606466647176511488, coefficient := 11295100318131606466647176511488 }, { argument := 722550783867271565138387271680, coefficient := 722550783867271565138387271680 }, { argument := 419545616439060908790031319040, coefficient := 419545616439060908790031319040 }, { argument := 736535637748573595431388315648, coefficient := 736535637748573595431388315648 }, { argument := 27969707762604060586002087936, coefficient := 27969707762604060586002087936 }, { argument := 722550783867271565138387271680, coefficient := 722550783867271565138387271680 }, { argument := 27969707762604060586002087936, coefficient := 27969707762604060586002087936 }, { argument := 736535637748573595431388315648, coefficient := 736535637748573595431388315648 }, { argument := 736535637748573595431388315648, coefficient := 736535637748573595431388315648 }, { argument := 27969707762604060586002087936, coefficient := 27969707762604060586002087936 }, { argument := 19093987165937705360044092030976, coefficient := (-19093987165937705360044092030976) }, { argument := 342599905872228991078332628992, coefficient := 342599905872228991078332628992 }, { argument := 390183226132260795394767716352, coefficient := 390183226132260795394767716352 }, { argument := 304533249664203547625184559104, coefficient := 304533249664203547625184559104 }, { argument := 4082648878310728810350130495488, coefficient := 4082648878310728810350130495488 }, { argument := 361633233976241712804906663936, coefficient := 361633233976241712804906663936 }, { argument := 304533249664203547625184559104, coefficient := 304533249664203547625184559104 }, { argument := 361633233976241712804906663936, coefficient := 361633233976241712804906663936 }, { argument := 352116569924235351941619646464, coefficient := 352116569924235351941619646464 }, { argument := 13304296344704892486875250425856, coefficient := 13304296344704892486875250425856 }, { argument := 352116569924235351941619646464, coefficient := 352116569924235351941619646464 }, { argument := 4082648878310728810350130495488, coefficient := 4082648878310728810350130495488 }, { argument := 13304296344704892486875250425856, coefficient := 13304296344704892486875250425856 }, { argument := 342599905872228991078332628992, coefficient := 342599905872228991078332628992 }, { argument := 352116569924235351941619646464, coefficient := 352116569924235351941619646464 }, { argument := 352116569924235351941619646464, coefficient := 352116569924235351941619646464 }, { argument := 390183226132260795394767716352, coefficient := 390183226132260795394767716352 }, { argument := 38980255957018054096023623565312, coefficient := (-38980255957018054096023623565312) }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 649918520624824644322040217600, coefficient := 649918520624824644322040217600 }, { argument := 33656494818071276223819939840, coefficient := 33656494818071276223819939840 }, { argument := 604656337938452928021040988160, coefficient := 604656337938452928021040988160 }, { argument := 905243653727434326019984588800, coefficient := 905243653727434326019984588800 }, { argument := 32495926031241232216102010880, coefficient := 32495926031241232216102010880 }, { argument := 906404222514264370027702517760, coefficient := 906404222514264370027702517760 }, { argument := 906404222514264370027702517760, coefficient := 906404222514264370027702517760 }, { argument := 648757951837994600314322288640, coefficient := 648757951837994600314322288640 }, { argument := 33656494818071276223819939840, coefficient := 33656494818071276223819939840 }, { argument := 4753689750855860255612637020160, coefficient := (-4753689750855860255612637020160) }, { argument := 37757171198204098384423288832, coefficient := 37757171198204098384423288832 }, { argument := 41470991316060239209120661504, coefficient := 41470991316060239209120661504 }, { argument := 37757171198204098384423288832, coefficient := 37757171198204098384423288832 }, { argument := 41470991316060239209120661504, coefficient := 41470991316060239209120661504 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 237684487542793012780631851008, coefficient := 237684487542793012780631851008 }] }

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


end Parent3

namespace Parent3

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1496599436833257273242574557020160)
def positiveArguments : Array ℕ := #[
    3, 22353473, 2612687025, 715310895, 25791501, 503003703,
    1006007037, 3223953, 11565, 5467635, 207547065, 21870555,
    11565, 47557, 8341051, 2085263, 11889
  ]
def positiveCoefficients : Array ℕ := #[
    237684487542793012780631851008, 3377961333469810457725848518656, 12338065637088406816176891494400, 3377960195379488086141352017920, 487187679461195749594742390784, 19002942622452140870282514530304,
    19002935652239212154686179115008, 487190002865505321460187529216, 3495306775960796601369231360, 413122820233039561727787663360, 3920453213495870566775610408960, 413123103575028533906500485120,
    3495306775960796601369231360, 449163165651663434855481344, 78778999348612674158688468992, 78779008793345639897978896384, 449153720918697695565053952
  ]
def positiveScales : Array ℕ := #[
    1, 24, 31, 29, 24, 28,
    29, 21, 13, 22, 27, 24,
    13, 15, 22, 20, 13
  ]
def negativeArguments : Array ℕ := #[
    3, 241, 123, 15, 1
  ]
def negativeCoefficients : Array ℕ := #[
    475368975085586025561263702016, 19093987165937705360044092030976, 38980255957018054096023623565312, 4753689750855860255612637020160, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    1, 7, 6, 3, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 24413995660748734, 31282887167881207, 29413995174681139, 24620392400976758, 28905993779664403,
    29905993250488811, 21620399281191558, 13497477645523536, 22382485506257545, 27628863289498412, 24382486495735546,
    13497477645523536, 15537370089131860, 22991797747512055, 20991797920475261, 13537339752689083
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    1584962500724866, 7912889341723050, 6942514514520450, 3906890600547867, 0
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
noncomputable def positiveFloor : ℝ := 11071173521 / 500000000000
noncomputable def negativeCeiling : ℝ := 5308767971 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 237684487542793012780631851008, coefficient := 237684487542793012780631851008 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 3377961333469810457725848518656, coefficient := 3377961333469810457725848518656 }, { argument := 12338065637088406816176891494400, coefficient := 12338065637088406816176891494400 }, { argument := 3377960195379488086141352017920, coefficient := 3377960195379488086141352017920 }, { argument := 19093987165937705360044092030976, coefficient := (-19093987165937705360044092030976) }, { argument := 487187679461195749594742390784, coefficient := 487187679461195749594742390784 }, { argument := 19002942622452140870282514530304, coefficient := 19002942622452140870282514530304 }, { argument := 19002935652239212154686179115008, coefficient := 19002935652239212154686179115008 }, { argument := 487190002865505321460187529216, coefficient := 487190002865505321460187529216 }, { argument := 38980255957018054096023623565312, coefficient := (-38980255957018054096023623565312) }, { argument := 3495306775960796601369231360, coefficient := 3495306775960796601369231360 }, { argument := 413122820233039561727787663360, coefficient := 413122820233039561727787663360 }, { argument := 3920453213495870566775610408960, coefficient := 3920453213495870566775610408960 }, { argument := 413123103575028533906500485120, coefficient := 413123103575028533906500485120 }, { argument := 3495306775960796601369231360, coefficient := 3495306775960796601369231360 }, { argument := 4753689750855860255612637020160, coefficient := (-4753689750855860255612637020160) }, { argument := 449163165651663434855481344, coefficient := 449163165651663434855481344 }, { argument := 78778999348612674158688468992, coefficient := 78778999348612674158688468992 }, { argument := 78779008793345639897978896384, coefficient := 78779008793345639897978896384 }, { argument := 449153720918697695565053952, coefficient := 449153720918697695565053952 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21
