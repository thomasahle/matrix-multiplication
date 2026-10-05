import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 5, branch 1,
parent chunk 4, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk4

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
def constantNumerator : ℤ := (-55419988332330865598984374714368)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    293019026559, 6349359738015, 12691704087951, 73217984301, 55841935967, 1833321916997,
    5011506255355, 457979815275, 13551637873, 55841935967, 120819061787, 966551942507,
    55843881243, 1001513831737, 21701565509145, 43379153025193, 250252773243, 120819061787,
    31587072368917, 345244477846481, 31566059901249, 937468950785, 1833321916997, 31587072368917,
    31587065916889, 1833386571743, 293019026559, 1001513831737, 36627449289, 36627449289,
    793671505065, 1586466084921, 9152265771, 966551942507, 31587065916889, 86311106204763,
    3945756657303, 117183564499, 5011506255355, 345244477846481, 86311106204763, 10023365414605,
    6349359738015, 21701565509145, 793671505065, 55843881243, 1833386571743, 10023365414605,
    915991916337, 27104216453, 457979815275, 31566059901249, 3945756657303, 915991916337,
    12691704087951, 43379153025193, 1586466084921, 13551637873, 937468950785, 117183564499,
    27104216453, 73217984301, 250252773243, 9152265771
  ]
def negativeCoefficients : Array ℕ := #[
    164955047352947233844625408, 7148743537541396026475151360, 7144794225149090549005811712, 164872243407401213019291648, 15718107625789268638564352, 516034243889865787317420032,
    5642454426045421943542251520, 515639431353924648016281600, 15257787818775675249098752, 15718107625789268638564352, 544120681643186132564836352, 544120371013594284172509184,
    15718655172306064436625408, 563802164927143853837778944, 24433790585085457575947796480, 24420292174988364885279113216, 563519148162804015918219264, 544120681643186132564836352,
    17781940918797436444794159104, 194355362722641661615849603072, 17770111951102469020412018688, 527748102178341981698129920, 516034243889865787317420032, 17781940918797436444794159104,
    17781937286628574371793338368, 516052442582990370696593408, 164955047352947233844625408, 563802164927143853837778944, 164955366969472138654777344, 164955366969472138654777344,
    7148757388930629457391124480, 7144808068886145263065890816, 164872562863485381104369664, 544120371013594284172509184, 17781937286628574371793338368, 194355332870852976013920436224,
    17770108211524444684485132288, 527747857411642883785621504, 5642454426045421943542251520, 194355362722641661615849603072, 194355332870852976013920436224, 5642653093276674393123061760,
    7148743537541396026475151360, 24433790585085457575947796480, 7148757388930629457391124480, 15718655172306064436625408, 516052442582990370696593408, 5642653093276674393123061760,
    515657606636212468416774144, 15258317389737508351246336, 515639431353924648016281600, 17770111951102469020412018688, 17770108211524444684485132288, 515657606636212468416774144,
    7144794225149090549005811712, 24420292174988364885279113216, 7144808068886145263065890816, 15257787818775675249098752, 527748102178341981698129920, 527747857411642883785621504,
    15258317389737508351246336, 164872243407401213019291648, 563519148162804015918219264, 164872562863485381104369664
  ]
def negativeScales : Array ℕ := #[
    38, 42, 43, 36, 35, 40,
    42, 38, 33, 35, 36, 39,
    35, 39, 44, 45, 37, 36,
    44, 48, 44, 39, 40, 44,
    44, 40, 38, 39, 35, 35,
    39, 40, 33, 39, 44, 46,
    41, 36, 42, 48, 46, 43,
    42, 44, 39, 35, 40, 43,
    39, 34, 38, 44, 41, 39,
    43, 45, 40, 33, 39, 36,
    34, 36, 37, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    38092203389743347, 42529748258193451, 43528951023297093, 36091479005512802, 35700629907714833, 40737597272912056,
    42188381422813416, 38736493059183819, 33657748177486355, 35700629907714833, 36814057133190032, 39814056309578795,
    35700680163693857, 39865319487065991, 44302864353201512, 45302067118305171, 37864595102804268, 36814057133190032,
    44844399462946469, 48294611667317086, 44843439428698619, 39769979952959760, 40737597272912056, 44844399462946469,
    44844399168259139, 40737648150739991, 38092203389743347, 39865319487065991, 35092206185103272, 35092206185103272,
    39529751053553376, 40528953818657018, 33091481800872727, 39814056309578795, 44844399168259139, 46294611445727981,
    41843439125094938, 36769979283845488, 42188381422813416, 48294611667317086, 46294611445727981, 43188432218293894,
    42529748258193451, 44302864353201512, 39529751053553376, 35700680163693857, 40737648150739991, 43188432218293894,
    39736543910468672, 34657798250023187, 38736493059183819, 44843439428698619, 41843439125094938, 39736543910468672,
    43528951023297093, 45302067118305171, 40528953818657018, 33657748177486355, 39769979952959760, 36769979283845488,
    34657798250023187, 36091479005512802, 37864595102804268, 33091481800872727
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
noncomputable def negativeCeiling : ℝ := 616561727 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 164955047352947233844625408, coefficient := (-164955047352947233844625408) }, { argument := 7148743537541396026475151360, coefficient := (-7148743537541396026475151360) }, { argument := 7144794225149090549005811712, coefficient := (-7144794225149090549005811712) }, { argument := 164872243407401213019291648, coefficient := (-164872243407401213019291648) }, { argument := 15718107625789268638564352, coefficient := (-15718107625789268638564352) }, { argument := 516034243889865787317420032, coefficient := (-516034243889865787317420032) }, { argument := 5642454426045421943542251520, coefficient := (-5642454426045421943542251520) }, { argument := 515639431353924648016281600, coefficient := (-515639431353924648016281600) }, { argument := 15257787818775675249098752, coefficient := (-15257787818775675249098752) }, { argument := 15718107625789268638564352, coefficient := (-15718107625789268638564352) }, { argument := 544120681643186132564836352, coefficient := (-544120681643186132564836352) }, { argument := 544120371013594284172509184, coefficient := (-544120371013594284172509184) }, { argument := 15718655172306064436625408, coefficient := (-15718655172306064436625408) }, { argument := 563802164927143853837778944, coefficient := (-563802164927143853837778944) }, { argument := 24433790585085457575947796480, coefficient := (-24433790585085457575947796480) }, { argument := 24420292174988364885279113216, coefficient := (-24420292174988364885279113216) }, { argument := 563519148162804015918219264, coefficient := (-563519148162804015918219264) }, { argument := 544120681643186132564836352, coefficient := (-544120681643186132564836352) }, { argument := 17781940918797436444794159104, coefficient := (-17781940918797436444794159104) }, { argument := 194355362722641661615849603072, coefficient := (-194355362722641661615849603072) }, { argument := 17770111951102469020412018688, coefficient := (-17770111951102469020412018688) }, { argument := 527748102178341981698129920, coefficient := (-527748102178341981698129920) }, { argument := 516034243889865787317420032, coefficient := (-516034243889865787317420032) }, { argument := 17781940918797436444794159104, coefficient := (-17781940918797436444794159104) }, { argument := 17781937286628574371793338368, coefficient := (-17781937286628574371793338368) }, { argument := 516052442582990370696593408, coefficient := (-516052442582990370696593408) }, { argument := 164955047352947233844625408, coefficient := (-164955047352947233844625408) }, { argument := 563802164927143853837778944, coefficient := (-563802164927143853837778944) }, { argument := 164955366969472138654777344, coefficient := (-164955366969472138654777344) }, { argument := 164955366969472138654777344, coefficient := (-164955366969472138654777344) }, { argument := 7148757388930629457391124480, coefficient := (-7148757388930629457391124480) }, { argument := 7144808068886145263065890816, coefficient := (-7144808068886145263065890816) }, { argument := 164872562863485381104369664, coefficient := (-164872562863485381104369664) }, { argument := 544120371013594284172509184, coefficient := (-544120371013594284172509184) }, { argument := 17781937286628574371793338368, coefficient := (-17781937286628574371793338368) }, { argument := 194355332870852976013920436224, coefficient := (-194355332870852976013920436224) }, { argument := 17770108211524444684485132288, coefficient := (-17770108211524444684485132288) }, { argument := 527747857411642883785621504, coefficient := (-527747857411642883785621504) }, { argument := 5642454426045421943542251520, coefficient := (-5642454426045421943542251520) }, { argument := 194355362722641661615849603072, coefficient := (-194355362722641661615849603072) }, { argument := 194355332870852976013920436224, coefficient := (-194355332870852976013920436224) }, { argument := 5642653093276674393123061760, coefficient := (-5642653093276674393123061760) }, { argument := 7148743537541396026475151360, coefficient := (-7148743537541396026475151360) }, { argument := 24433790585085457575947796480, coefficient := (-24433790585085457575947796480) }, { argument := 7148757388930629457391124480, coefficient := (-7148757388930629457391124480) }, { argument := 15718655172306064436625408, coefficient := (-15718655172306064436625408) }, { argument := 516052442582990370696593408, coefficient := (-516052442582990370696593408) }, { argument := 5642653093276674393123061760, coefficient := (-5642653093276674393123061760) }, { argument := 515657606636212468416774144, coefficient := (-515657606636212468416774144) }, { argument := 15258317389737508351246336, coefficient := (-15258317389737508351246336) }, { argument := 515639431353924648016281600, coefficient := (-515639431353924648016281600) }, { argument := 17770111951102469020412018688, coefficient := (-17770111951102469020412018688) }, { argument := 17770108211524444684485132288, coefficient := (-17770108211524444684485132288) }, { argument := 515657606636212468416774144, coefficient := (-515657606636212468416774144) }, { argument := 7144794225149090549005811712, coefficient := (-7144794225149090549005811712) }, { argument := 24420292174988364885279113216, coefficient := (-24420292174988364885279113216) }, { argument := 7144808068886145263065890816, coefficient := (-7144808068886145263065890816) }, { argument := 15257787818775675249098752, coefficient := (-15257787818775675249098752) }, { argument := 527748102178341981698129920, coefficient := (-527748102178341981698129920) }, { argument := 527747857411642883785621504, coefficient := (-527747857411642883785621504) }, { argument := 15258317389737508351246336, coefficient := (-15258317389737508351246336) }, { argument := 164872243407401213019291648, coefficient := (-164872243407401213019291648) }, { argument := 563519148162804015918219264, coefficient := (-563519148162804015918219264) }, { argument := 164872562863485381104369664, coefficient := (-164872562863485381104369664) }] }

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
def constantNumerator : ℤ := 54943386831478089008966396805120
def positiveArguments : Array ℕ := #[
    7, 1548309, 5291987, 193539, 1419861, 24455883,
    24455879, 1419911, 237101, 7749497, 42351203, 121005,
    57493, 189251, 4100835, 8197139, 47289
  ]
def positiveCoefficients : Array ℕ := #[
    1109194275199700726309615304704, 29246730106901670044689760256, 99962808146327540661965815808, 29246786775299464480432324608, 13410207993467554645527232512, 461958568752726190390637494272,
    461958493194862464476314075136, 13410680230115841610048602112, 2239355630909751499625070592, 73191929783797733949203021824, 799991606225633467932870705152, 73143034401234101642660413440,
    2172024129596996098168193024, 1787425158499126452674363392, 77462583023114966119628144640, 77419788938047201394701631488, 1786527908867381220083761152
  ]
def positiveScales : Array ℕ := #[
    2, 20, 22, 17, 20, 24,
    24, 20, 17, 22, 25, 16,
    15, 17, 21, 22, 15
  ]
def negativeArguments : Array ℕ := #[
    1, 3, 3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 950737950171172051122527404032, 950737950171172051122527404032, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 1, 1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2807354922011143, 20562261991892082, 22335378086900973, 17562264787252007, 20437318270584958, 24543678219532159,
    24543677983565188, 20437369073784688, 17855142221879143, 22885671240901876, 25335899614583280, 16884707135997771,
    15811098692425069, 17529941397851098, 21967486265438996, 22966689030553932, 15529217013620555
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 1584962500724866, 1584962500724866, 0
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
noncomputable def positiveFloor : ℝ := 135965329 / 200000000000
noncomputable def negativeCeiling : ℝ := 36276913 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1109194275199700726309615304704, coefficient := 1109194275199700726309615304704 }, { argument := 29246730106901670044689760256, coefficient := 29246730106901670044689760256 }, { argument := 99962808146327540661965815808, coefficient := 99962808146327540661965815808 }, { argument := 29246786775299464480432324608, coefficient := 29246786775299464480432324608 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 13410207993467554645527232512, coefficient := 13410207993467554645527232512 }, { argument := 461958568752726190390637494272, coefficient := 461958568752726190390637494272 }, { argument := 461958493194862464476314075136, coefficient := 461958493194862464476314075136 }, { argument := 13410680230115841610048602112, coefficient := 13410680230115841610048602112 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 2239355630909751499625070592, coefficient := 2239355630909751499625070592 }, { argument := 73191929783797733949203021824, coefficient := 73191929783797733949203021824 }, { argument := 799991606225633467932870705152, coefficient := 799991606225633467932870705152 }, { argument := 73143034401234101642660413440, coefficient := 73143034401234101642660413440 }, { argument := 2172024129596996098168193024, coefficient := 2172024129596996098168193024 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 1787425158499126452674363392, coefficient := 1787425158499126452674363392 }, { argument := 77462583023114966119628144640, coefficient := 77462583023114966119628144640 }, { argument := 77419788938047201394701631488, coefficient := 77419788938047201394701631488 }, { argument := 1786527908867381220083761152, coefficient := 1786527908867381220083761152 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region5.Branch1.Chunk4
