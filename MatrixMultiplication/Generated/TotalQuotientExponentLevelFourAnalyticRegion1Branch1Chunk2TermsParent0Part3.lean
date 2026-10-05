import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 2, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2

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
def constantNumerator : ℤ := 1370415096042982188787187618676736
def positiveArguments : Array ℕ := #[
    187, 31, 35, 15, 395, 35,
    15, 35, 35, 1451, 9, 395,
    1451, 31, 35, 9, 35
  ]
def positiveCoefficients : Array ℕ := #[
    14815666390167431129992718712832, 1199254413057712141308526592, 1353996917968384675670917120, 1160568786830044007717928960, 15280822359928912768286064640, 1353996917968384675670917120,
    1160568786830044007717928960, 1353996917968384675670917120, 1353996917968384675670917120, 56132843656346461839957164032, 1392682544196052809261514752, 15280822359928912768286064640,
    56132843656346461839957164032, 1199254413057712141308526592, 1353996917968384675670917120, 1392682544196052809261514752, 1353996917968384675670917120
  ]
def positiveScales : Array ℕ := #[
    7, 4, 5, 3, 8, 5,
    3, 5, 5, 10, 3, 8,
    10, 4, 5, 3, 5
  ]
def negativeArguments : Array ℕ := #[
    6438699, 2765735, 113312675, 2333195725, 113312675, 2765735,
    585975757, 35, 5222740105, 395, 35, 10445477665,
    35, 35, 1451, 9, 395, 1451,
    585975757, 35, 9, 35, 902503, 36975715,
    761358605, 36975715, 902503, 1179116049, 35, 10517089405,
    395, 35, 21034173685, 35, 35, 1451,
    9, 395, 1451, 1179116049, 35, 9,
    35, 743307, 5415379, 1486615, 1
  ]
def negativeCoefficients : Array ℕ := #[
    118773032620649616280387584, 204075222882804346954711040, 33443998656518823466552524800, 344318915303585685776944332800, 33443998656518823466552524800, 204075222882804346954711040,
    1351168102847152288289521664, 169249614746048084458864640, 48171275040216975673225379840, 1910102794991114096035758080, 169249614746048084458864640, 48171263303476058775523164160,
    169249614746048084458864640, 169249614746048084458864640, 7016605457043307729994645504, 174085318024506601157689344, 1910102794991114096035758080, 7016605457043307729994645504,
    1351168102847152288289521664, 169249614746048084458864640, 174085318024506601157689344, 169249614746048084458864640, 8324120933377545731047424, 1364163103094846746662010880,
    14044587334751521393533255680, 1364163103094846746662010880, 8324120933377545731047424, 1359428249319160704688717824, 169249614746048084458864640, 48501514163589316086983557120,
    1910102794991114096035758080, 169249614746048084458864640, 48501502346143893866802053120, 169249614746048084458864640, 169249614746048084458864640, 7016605457043307729994645504,
    174085318024506601157689344, 1910102794991114096035758080, 7016605457043307729994645504, 1359428249319160704688717824, 169249614746048084458864640, 174085318024506601157689344,
    169249614746048084458864640, 14040672253129549499426930688, 51146808563272272855399661568, 14040681697862515238717358080, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    22, 21, 26, 31, 26, 21,
    29, 5, 32, 8, 5, 33,
    5, 5, 10, 3, 8, 10,
    29, 5, 3, 5, 19, 25,
    29, 25, 19, 30, 5, 33,
    8, 5, 34, 5, 5, 10,
    3, 8, 10, 30, 5, 3,
    5, 19, 22, 20, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7546894459887560, 4954196309696329, 5129283016944966, 3906890595303263, 8625708843063759, 5129283016944966,
    3906890595303263, 5129283016944966, 5129283016944966, 10502831804066725, 3169925001442312, 8625708843063759,
    10502831804066725, 4954196309696329, 5129283016944966, 3169925001442312, 5129283016944966
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    22618337776949349, 21399231500034915, 26755734007421834, 31119660189873691, 26755734007421834, 21399231500034915,
    29126265737774810, 5129283016944967, 32282159767813865, 8625708843075807, 5129283016944967, 33282159416306874,
    5129283016944967, 5129283016944967, 10502831804067043, 3169925001442313, 8625708843075807, 10502831804067043,
    29126265737774810, 5129283016944967, 3169925001442313, 5129283016944967, 19783572202551266, 25140074709222989,
    29504000891929928, 25140074709222989, 19783572202551266, 30135058569825227, 5129283016944967, 33292016444191326,
    8625708843075807, 5129283016944967, 34292016092677104, 5129283016944967, 5129283016944967, 10502831804067043,
    3169925001442313, 8625708843075807, 10502831804067043, 30135058569825227, 5129283016944967, 3169925001442313,
    5129283016944967, 19503598668916132, 22368630878955852, 20503599639372859, 0
  ]

abbrev PositiveTerm := Fin 17
abbrev NegativeTerm := Fin 47
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
noncomputable def positiveFloor : ℝ := 1364117459 / 1000000000000
noncomputable def negativeCeiling : ℝ := 260908627 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 118773032620649616280387584, coefficient := (-118773032620649616280387584) }, { argument := 204075222882804346954711040, coefficient := (-204075222882804346954711040) }, { argument := 33443998656518823466552524800, coefficient := (-33443998656518823466552524800) }, { argument := 344318915303585685776944332800, coefficient := (-344318915303585685776944332800) }, { argument := 33443998656518823466552524800, coefficient := (-33443998656518823466552524800) }, { argument := 204075222882804346954711040, coefficient := (-204075222882804346954711040) }, { argument := 1351168102847152288289521664, coefficient := (-1351168102847152288289521664) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 48171275040216975673225379840, coefficient := (-48171275040216975673225379840) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 48171263303476058775523164160, coefficient := (-48171263303476058775523164160) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 174085318024506601157689344, coefficient := (-174085318024506601157689344) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 1351168102847152288289521664, coefficient := (-1351168102847152288289521664) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 174085318024506601157689344, coefficient := (-174085318024506601157689344) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 8324120933377545731047424, coefficient := (-8324120933377545731047424) }, { argument := 1364163103094846746662010880, coefficient := (-1364163103094846746662010880) }, { argument := 14044587334751521393533255680, coefficient := (-14044587334751521393533255680) }, { argument := 1364163103094846746662010880, coefficient := (-1364163103094846746662010880) }, { argument := 8324120933377545731047424, coefficient := (-8324120933377545731047424) }, { argument := 1359428249319160704688717824, coefficient := (-1359428249319160704688717824) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 48501514163589316086983557120, coefficient := (-48501514163589316086983557120) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 48501502346143893866802053120, coefficient := (-48501502346143893866802053120) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 174085318024506601157689344, coefficient := (-174085318024506601157689344) }, { argument := 1910102794991114096035758080, coefficient := (-1910102794991114096035758080) }, { argument := 7016605457043307729994645504, coefficient := (-7016605457043307729994645504) }, { argument := 1359428249319160704688717824, coefficient := (-1359428249319160704688717824) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 174085318024506601157689344, coefficient := (-174085318024506601157689344) }, { argument := 169249614746048084458864640, coefficient := (-169249614746048084458864640) }, { argument := 14040672253129549499426930688, coefficient := (-14040672253129549499426930688) }, { argument := 51146808563272272855399661568, coefficient := (-51146808563272272855399661568) }, { argument := 14040681697862515238717358080, coefficient := (-14040681697862515238717358080) }, { argument := 14815666390167431129992718712832, coefficient := 14815666390167431129992718712832 }, { argument := 1199254413057712141308526592, coefficient := 1199254413057712141308526592 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 15280822359928912768286064640, coefficient := 15280822359928912768286064640 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 56132843656346461839957164032, coefficient := 56132843656346461839957164032 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 15280822359928912768286064640, coefficient := 15280822359928912768286064640 }, { argument := 56132843656346461839957164032, coefficient := 56132843656346461839957164032 }, { argument := 1199254413057712141308526592, coefficient := 1199254413057712141308526592 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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
def constantNumerator : ℤ := (-169267569296752750438838597320704)
def positiveArguments : Array ℕ := #[
    27, 783, 693, 45, 27, 45,
    1377, 45, 27, 22059, 1413, 783,
    1377, 45, 1413, 45, 1377, 45,
    27, 4653, 3465, 3663, 297, 63657,
    115137, 3465, 63657, 1881, 1881, 3663,
    3663, 115137, 3663, 4653, 297, 217,
    665, 1967, 4389, 217, 2191, 4459,
    217, 665, 217, 1285, 5125, 2545,
    5125, 1, 1, 1, 1, 1,
    743307, 5415379, 1486615
  ]
def positiveCoefficients : Array ℕ := #[
    2089023816294079213892272128, 30290845336264148601437945856, 53618277951548033156568317952, 1740853180245066011576893440, 33424381060705267422276354048, 1740853180245066011576893440,
    53270107315499019954252939264, 55707301767842112370460590080, 33424381060705267422276354048, 853366228956131358874993164288, 54662789859695072763514454016, 30290845336264148601437945856,
    53270107315499019954252939264, 1740853180245066011576893440, 54662789859695072763514454016, 1740853180245066011576893440, 53270107315499019954252939264, 55707301767842112370460590080,
    2089023816294079213892272128, 90002109418669912798525390848, 67022847439435041445710397440, 70852724435974186671179563008, 91917047916939485411259973632, 1231305454387335189988336730112,
    2227073473487512948610319777792, 67022847439435041445710397440, 1231305454387335189988336730112, 72767662934243759283914145792, 72767662934243759283914145792, 70852724435974186671179563008,
    70852724435974186671179563008, 2227073473487512948610319777792, 70852724435974186671179563008, 90002109418669912798525390848, 91917047916939485411259973632, 33579123565615939956638744576,
    823230126124777882807917608960, 608757014318585750181644337152, 679164854052941753316532027392, 33579123565615939956638744576, 678081656518567045575995293696, 689996829396688830721899364352,
    33579123565615939956638744576, 823230126124777882807917608960, 33579123565615939956638744576, 198844118810214206655671828480, 198263834416799184651812864000, 196909837498830799976141946880,
    198263834416799184651812864000, 158456325028528675187087900672, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168,
    28081344506259098998853861376, 102293617126544545710799323136, 28081363395725030477434716160
  ]
def positiveScales : Array ℕ := #[
    4, 9, 9, 5, 4, 5,
    10, 5, 4, 14, 10, 9,
    10, 5, 10, 5, 10, 5,
    4, 12, 11, 11, 8, 15,
    16, 11, 15, 10, 10, 11,
    11, 16, 11, 12, 8, 7,
    9, 10, 12, 7, 11, 12,
    7, 9, 7, 10, 12, 11,
    12, 0, 0, 0, 0, 0,
    19, 22, 20
  ]
def negativeArguments : Array ℕ := #[
    9, 99, 7, 5, 1, 1,
    1
  ]
def negativeCoefficients : Array ℕ := #[
    1426106925256758076683791106048, 7843588088912169421760851083264, 4436777100798802905238461218816, 792281625142643375935439503360, 158456325028528675187087900672, 158456325028528675187087900672,
    158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    3, 6, 2, 2, 0, 0,
    0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4754887502147955, 9612868497290540, 9436711542137211, 5491853096329661, 4754887502147955, 5491853096329661,
    10427312844134962, 5491853096329661, 4754887502147955, 14429079770309150, 10464545750333933, 9612868497290540,
    10427312844134962, 5491853096329661, 10464545750333933, 5491853096329661, 10427312844134962, 5491853096329661,
    4754887502147955, 12183945471757246, 11758639637007751, 11838809985622091, 8214319120800765, 15958031546671225,
    16812992001500797, 11758639637007751, 15958031546671225, 10877284133344468, 10877284133344468, 11838809985622091,
    11838809985622091, 16812992001500797, 11838809985622091, 12183945471757246, 8214319120800765, 7761551232426566,
    9377210530388551, 10941781241718677, 12099676554859642, 7761551232426566, 11097373768990222, 12122504484313904,
    7761551232426566, 9377210530388551, 7761551232426566, 10327552644081240, 12323336289280170, 11313449940963057,
    12323336289280170, 0, 0, 0, 0, 0,
    19503598668915806, 22368630878955848, 20503599639372533
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    3169925001442313, 6629356620092098, 2807354922807594, 2321928094887363, 0, 0,
    0
  ]

abbrev PositiveTerm := Fin 57
abbrev NegativeTerm := Fin 7
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
noncomputable def positiveFloor : ℝ := 2424658271 / 1000000000000
noncomputable def negativeCeiling : ℝ := 852390397 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2089023816294079213892272128, coefficient := 2089023816294079213892272128 }, { argument := 30290845336264148601437945856, coefficient := 30290845336264148601437945856 }, { argument := 53618277951548033156568317952, coefficient := 53618277951548033156568317952 }, { argument := 1740853180245066011576893440, coefficient := 1740853180245066011576893440 }, { argument := 33424381060705267422276354048, coefficient := 33424381060705267422276354048 }, { argument := 1740853180245066011576893440, coefficient := 1740853180245066011576893440 }, { argument := 53270107315499019954252939264, coefficient := 53270107315499019954252939264 }, { argument := 55707301767842112370460590080, coefficient := 55707301767842112370460590080 }, { argument := 33424381060705267422276354048, coefficient := 33424381060705267422276354048 }, { argument := 853366228956131358874993164288, coefficient := 853366228956131358874993164288 }, { argument := 54662789859695072763514454016, coefficient := 54662789859695072763514454016 }, { argument := 30290845336264148601437945856, coefficient := 30290845336264148601437945856 }, { argument := 53270107315499019954252939264, coefficient := 53270107315499019954252939264 }, { argument := 1740853180245066011576893440, coefficient := 1740853180245066011576893440 }, { argument := 54662789859695072763514454016, coefficient := 54662789859695072763514454016 }, { argument := 1740853180245066011576893440, coefficient := 1740853180245066011576893440 }, { argument := 53270107315499019954252939264, coefficient := 53270107315499019954252939264 }, { argument := 55707301767842112370460590080, coefficient := 55707301767842112370460590080 }, { argument := 2089023816294079213892272128, coefficient := 2089023816294079213892272128 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 90002109418669912798525390848, coefficient := 90002109418669912798525390848 }, { argument := 67022847439435041445710397440, coefficient := 67022847439435041445710397440 }, { argument := 70852724435974186671179563008, coefficient := 70852724435974186671179563008 }, { argument := 91917047916939485411259973632, coefficient := 91917047916939485411259973632 }, { argument := 1231305454387335189988336730112, coefficient := 1231305454387335189988336730112 }, { argument := 2227073473487512948610319777792, coefficient := 2227073473487512948610319777792 }, { argument := 67022847439435041445710397440, coefficient := 67022847439435041445710397440 }, { argument := 1231305454387335189988336730112, coefficient := 1231305454387335189988336730112 }, { argument := 72767662934243759283914145792, coefficient := 72767662934243759283914145792 }, { argument := 72767662934243759283914145792, coefficient := 72767662934243759283914145792 }, { argument := 70852724435974186671179563008, coefficient := 70852724435974186671179563008 }, { argument := 70852724435974186671179563008, coefficient := 70852724435974186671179563008 }, { argument := 2227073473487512948610319777792, coefficient := 2227073473487512948610319777792 }, { argument := 70852724435974186671179563008, coefficient := 70852724435974186671179563008 }, { argument := 90002109418669912798525390848, coefficient := 90002109418669912798525390848 }, { argument := 91917047916939485411259973632, coefficient := 91917047916939485411259973632 }, { argument := 7843588088912169421760851083264, coefficient := (-7843588088912169421760851083264) }, { argument := 33579123565615939956638744576, coefficient := 33579123565615939956638744576 }, { argument := 823230126124777882807917608960, coefficient := 823230126124777882807917608960 }, { argument := 608757014318585750181644337152, coefficient := 608757014318585750181644337152 }, { argument := 679164854052941753316532027392, coefficient := 679164854052941753316532027392 }, { argument := 33579123565615939956638744576, coefficient := 33579123565615939956638744576 }, { argument := 678081656518567045575995293696, coefficient := 678081656518567045575995293696 }, { argument := 689996829396688830721899364352, coefficient := 689996829396688830721899364352 }, { argument := 33579123565615939956638744576, coefficient := 33579123565615939956638744576 }, { argument := 823230126124777882807917608960, coefficient := 823230126124777882807917608960 }, { argument := 33579123565615939956638744576, coefficient := 33579123565615939956638744576 }, { argument := 4436777100798802905238461218816, coefficient := (-4436777100798802905238461218816) }, { argument := 198844118810214206655671828480, coefficient := 198844118810214206655671828480 }, { argument := 198263834416799184651812864000, coefficient := 198263834416799184651812864000 }, { argument := 196909837498830799976141946880, coefficient := 196909837498830799976141946880 }, { argument := 198263834416799184651812864000, coefficient := 198263834416799184651812864000 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 28081344506259098998853861376, coefficient := 28081344506259098998853861376 }, { argument := 102293617126544545710799323136, coefficient := 102293617126544545710799323136 }, { argument := 28081363395725030477434716160, coefficient := 28081363395725030477434716160 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk2
