import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 15, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-180339360843289180096305037261668352)
def positiveArguments : Array ℕ := #[
    91, 91, 3, 3, 57, 87,
    897, 27, 87, 27, 27, 2313,
    27, 897, 2313, 3, 27, 27,
    57, 3007, 104371080483, 104371040989, 161648627309, 279944475255,
    161648626853, 5542942463, 141, 101550301677, 3489, 111,
    50773813223, 57, 57, 1929, 105, 3489,
    1929, 5548295563, 111, 105, 141, 30080629,
    4012524399, 153, 41849092761, 157, 5, 153,
    87, 157, 2451, 3, 2006262593, 153,
    5, 3, 5, 77
  ]
def positiveCoefficients : Array ℕ := #[
    56326271787484802507910152192, 56326271787484802507910152192, 1856910058928070412348686336, 3713820117856140824697372672, 4410161389954167229328130048, 3365649481807127622381993984,
    34701006726218315830766075904, 4178047632588158427784544256, 3365649481807127622381993984, 4178047632588158427784544256, 4178047632588158427784544256, 178959706929192785990104645632,
    4178047632588158427784544256, 34701006726218315830766075904, 178959706929192785990104645632, 3713820117856140824697372672, 4178047632588158427784544256, 4178047632588158427784544256,
    4410161389954167229328130048, 238239084680392863143786658660352, 985756984507618762792641899790336, 985756611497335013885105760370688, 763364059605908411977800366424064, 2644000814017485551832298118184960,
    763364057452509295789242148978688, 26175805703746118548740267573248, 5454673298101206836274266112, 959115481929531848233575864336384, 134974149908334118097595138048, 4294104511271162828556337152,
    959090215087115180545906502008832, 4410161389954167229328130048, 4410161389954167229328130048, 74624572993171829696262832128, 4061990753905154027012751360, 134974149908334118097595138048,
    74624572993171829696262832128, 26201085003765568046533703630848, 4294104511271162828556337152, 4061990753905154027012751360, 5454673298101206836274266112, 142051754173236653034815094784,
    18948610733534266956428768968704, 47351206502665795514891501568, 197626752993049100019123571654656, 48589146541951175789790625792, 1547425049106725343623905280, 47351206502665795514891501568,
    26925195854457020979055951872, 48589146541951175789790625792, 758547759072116763444438368256, 29710560942849126597578981376, 18948614450036688974839552147456, 47351206502665795514891501568,
    1547425049106725343623905280, 29710560942849126597578981376, 1547425049106725343623905280, 47660691512487140583616282624
  ]
def positiveScales : Array ℕ := #[
    6, 6, 1, 1, 5, 6,
    9, 4, 6, 4, 4, 11,
    4, 9, 11, 1, 4, 4,
    5, 11, 36, 36, 37, 38,
    37, 32, 7, 36, 11, 6,
    35, 5, 5, 10, 6, 11,
    10, 32, 6, 6, 7, 24,
    31, 7, 35, 7, 2, 7,
    6, 7, 11, 1, 30, 7,
    2, 1, 2, 6
  ]
def negativeArguments : Array ℕ := #[
    1, 3, 3007, 6221, 26321, 12439
  ]
def negativeCoefficients : Array ℕ := #[
    1267650600228229401496703205376, 475368975085586025561263702016, 238239084680392863143786658660352, 1971513596004953776677747660161024, 4170728931075903259599340633587712, 1971038227029868190652186396459008
  ]
def negativeScales : Array ℕ := #[
    0, 1, 11, 12, 14, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6507794640198673, 6507794640198673, 1584962500720924, 1584962500720924, 5832890014087662, 6442943495848725,
    9808964174871270, 4754887502147955, 6442943495848725, 4754887502147955, 4754887502147955, 11175549550636190,
    4754887502147955, 9808964174871270, 11175549550636190, 1584962500720924, 4754887502147955, 4754887502147955,
    5832890014087662, 11554109152573908, 36602931063872668, 36602930517956994, 37234070300170812, 38026349752296038,
    37234070296101065, 32368004886187119, 7139551352398793, 36563403569237028, 11768597882173550, 6794415866314396,
    35563365562522407, 5832890014087662, 5832890014087662, 10913637427705176, 6714245517659862, 11768597882173550,
    10913637427705176, 32369397497436638, 6794415866314396, 6714245517659862, 7139551352398793, 24842331398876991,
    31901863018579915, 7257387842692651, 35284477296060389, 7294620748891626, 2321928094887362, 7257387842692651,
    6442943495848725, 7294620748891626, 11259154768866839, 1584962500720924, 30901863301544146, 7257387842692651,
    2321928094887362, 1584962500720924, 2321928094887362, 6266786540694901
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 1584962500724866, 11554109152575509, 12602930790921371, 14683926681272074, 13602582888092355
  ]

abbrev PositiveTerm := Fin 58
abbrev NegativeTerm := Fin 6
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
noncomputable def positiveFloor : ℝ := 749582693769 / 200000000000
noncomputable def negativeCeiling : ℝ := 1392135974163 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 56326271787484802507910152192, coefficient := 56326271787484802507910152192 }, { argument := 56326271787484802507910152192, coefficient := 56326271787484802507910152192 }, { argument := 1856910058928070412348686336, coefficient := 1856910058928070412348686336 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 34701006726218315830766075904, coefficient := 34701006726218315830766075904 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 3365649481807127622381993984, coefficient := 3365649481807127622381993984 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 178959706929192785990104645632, coefficient := 178959706929192785990104645632 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 34701006726218315830766075904, coefficient := 34701006726218315830766075904 }, { argument := 178959706929192785990104645632, coefficient := 178959706929192785990104645632 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 238239084680392863143786658660352, coefficient := 238239084680392863143786658660352 }, { argument := 238239084680392863143786658660352, coefficient := (-238239084680392863143786658660352) }, { argument := 985756984507618762792641899790336, coefficient := 985756984507618762792641899790336 }, { argument := 985756611497335013885105760370688, coefficient := 985756611497335013885105760370688 }, { argument := 1971513596004953776677747660161024, coefficient := (-1971513596004953776677747660161024) }, { argument := 763364059605908411977800366424064, coefficient := 763364059605908411977800366424064 }, { argument := 2644000814017485551832298118184960, coefficient := 2644000814017485551832298118184960 }, { argument := 763364057452509295789242148978688, coefficient := 763364057452509295789242148978688 }, { argument := 4170728931075903259599340633587712, coefficient := (-4170728931075903259599340633587712) }, { argument := 26175805703746118548740267573248, coefficient := 26175805703746118548740267573248 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 959115481929531848233575864336384, coefficient := 959115481929531848233575864336384 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 959090215087115180545906502008832, coefficient := 959090215087115180545906502008832 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 26201085003765568046533703630848, coefficient := 26201085003765568046533703630848 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 1971038227029868190652186396459008, coefficient := (-1971038227029868190652186396459008) }, { argument := 142051754173236653034815094784, coefficient := 142051754173236653034815094784 }, { argument := 18948610733534266956428768968704, coefficient := 18948610733534266956428768968704 }, { argument := 47351206502665795514891501568, coefficient := 47351206502665795514891501568 }, { argument := 197626752993049100019123571654656, coefficient := 197626752993049100019123571654656 }, { argument := 48589146541951175789790625792, coefficient := 48589146541951175789790625792 }, { argument := 1547425049106725343623905280, coefficient := 1547425049106725343623905280 }, { argument := 47351206502665795514891501568, coefficient := 47351206502665795514891501568 }, { argument := 26925195854457020979055951872, coefficient := 26925195854457020979055951872 }, { argument := 48589146541951175789790625792, coefficient := 48589146541951175789790625792 }, { argument := 758547759072116763444438368256, coefficient := 758547759072116763444438368256 }, { argument := 29710560942849126597578981376, coefficient := 29710560942849126597578981376 }, { argument := 18948614450036688974839552147456, coefficient := 18948614450036688974839552147456 }, { argument := 47351206502665795514891501568, coefficient := 47351206502665795514891501568 }, { argument := 1547425049106725343623905280, coefficient := 1547425049106725343623905280 }, { argument := 29710560942849126597578981376, coefficient := 29710560942849126597578981376 }, { argument := 1547425049106725343623905280, coefficient := 1547425049106725343623905280 }, { argument := 47660691512487140583616282624, coefficient := 47660691512487140583616282624 }] }

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


end Parent3

namespace Parent3

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-22736660654644003459575749516722176)
def positiveArguments : Array ℕ := #[
    87, 30080257
  ]
def positiveCoefficients : Array ℕ := #[
    26925195854457020979055951872, 142049997452905025526795599872
  ]
def positiveScales : Array ℕ := #[
    6, 24
  ]
def negativeArguments : Array ℕ := #[
    2991
  ]
def negativeCoefficients : Array ℕ := #[
    236971434080164633742289955454976
  ]
def negativeScales : Array ℕ := #[
    11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6442943495848725, 24842313557299516
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    11546412195120545
  ]

abbrev PositiveTerm := Fin 2
abbrev NegativeTerm := Fin 1
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
noncomputable def positiveFloor : ℝ := 44565153 / 1000000000000
noncomputable def negativeCeiling : ℝ := 32935446621 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 26925195854457020979055951872, coefficient := 26925195854457020979055951872 }, { argument := 142049997452905025526795599872, coefficient := 142049997452905025526795599872 }, { argument := 236971434080164633742289955454976, coefficient := (-236971434080164633742289955454976) }] }

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

end TermShard3


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15
