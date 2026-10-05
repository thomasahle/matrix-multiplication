import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 10, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 128834904332440468941848355371220992
def positiveArguments : Array ℕ := #[
    17027, 1, 1, 1, 1, 1,
    2511
  ]
def positiveCoefficients : Array ℕ := #[
    1349017923130378876205272842371072, 158456325028528675187087900672, 158456325028528675187087900672, 158456325028528675187087900672, 158456325028528675187087900672, 158456325028528675187087900672,
    48569803728837341722995326976
  ]
def positiveScales : Array ℕ := #[
    14, 0, 0, 0, 0, 0,
    11
  ]
def negativeArguments : Array ℕ := #[
    1655158877031, 46592035977, 197747542719, 349718181185, 197747542719, 4048367511,
    72705726069, 72705735513, 4048366797, 159038238963, 279274917645, 159038238963,
    18845010317, 18845005427, 1128033757261, 137462262620171, 4797, 1385062876385279,
    29169, 2745, 4797, 15327, 29169, 269721,
    15741, 68731141462021, 4797, 2745, 15741, 2745,
    38493, 15327, 1143104419743, 9564493683861, 351226991376747, 702431190420549,
    19151801173947, 29113895020677, 50049359878011, 29113895020677, 4547100911, 81495083557,
    40747548219, 4547097051, 165449840157, 289455983075, 165449840157, 19809700467,
    19809695117, 919980351, 1613379265, 919980351, 18845010317, 18845005427,
    1, 1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    3816536525739919467899636416512, 107433920442598371092651311104, 227987394483896227686455967744, 806395223280360245888674693120, 227987394483896227686455967744, 4667449961983596125786996736,
    167647990186009475557714034688, 167648011962390854571839717376, 4667449138797641836498255872, 183358605755245234735061925888, 643964116500453354651034583040, 183358605755245234735061925888,
    86907270596028777166241005568, 86907248044884147056314155008, 317513275553873758536073216, 38692187169606711045496242176, 1449804289172844037766381568, 389860540873340616758760833024,
    1101973663510597449906388992, 51851583981908704446382080, 1449804289172844037766381568, 1158075377327088835045097472, 1101973663510597449906388992, 20379542562017337226932781056,
    1189356332909617364940619776, 38692192884638327906659991552, 1449804289172844037766381568, 51851583981908704446382080, 1189356332909617364940619776, 51851583981908704446382080,
    1454224424200810025686401024, 1158075377327088835045097472, 321755289925008865684881408, 21537325095311931085871382528, 790892873743389100535244128256, 790867211857849598965318680576,
    21563011157615384261377916928, 131117326766424676137059745792, 450804556993484385478521126912, 131117326766424676137059745792, 5242450423909284581407195136, 187914868705194309486865547264,
    187914898406758111168457342976, 5242445973632276798977867776, 190750678650770771306958815232, 667440055048566065628341862400, 190750678650770771306958815232, 91356118672898396767458951168,
    91356094000378198180933664768, 8485321043869241583870148608, 29761594395284622209701642240, 8485321043869241583870148608, 86907270596028777166241005568, 86907248044884147056314155008,
    79228162514264337593543950336, 158456325028528675187087900672, 633825300114114700748351602688
  ]
def negativeScales : Array ℕ := #[
    40, 35, 37, 38, 37, 31,
    36, 36, 31, 37, 38, 37,
    34, 34, 40, 46, 12, 50,
    14, 11, 12, 13, 14, 18,
    13, 45, 12, 11, 13, 11,
    15, 13, 40, 43, 48, 49,
    44, 44, 45, 44, 32, 36,
    35, 32, 37, 38, 37, 34,
    34, 29, 30, 29, 34, 34,
    0, 0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14055536647426470, 0, 0, 0, 0, 0,
    11294046313271499
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    40590106845173658, 35439364323530016, 37524868811131526, 38347401844725423, 37524868811131526, 31914693123560199,
    36081349939511448, 36081350126908120, 31914692869115796, 37210582730840392, 38022895051270334, 37210582730840392,
    34133463533702408, 34133463159344445, 40036947380768316, 46966028953394132, 12227916724201489, 50298872893729469,
    14832148307987232, 11422590433892578, 12227916724201489, 13903787725794627, 14832148307987232, 18041108326067460,
    13942239584502269, 45966029166487514, 12227916724201489, 11422590433892578, 13942239584502269, 11422590433892578,
    15232308493318647, 13903787725794627, 40056094334820710, 43120825737212762, 48319397046955463, 49319350235463192,
    44122545313546221, 44726773097902339, 45508416850914525, 44726773097902339, 32082299875263312, 36245993975801609,
    35245994203831970, 32082298650569747, 37267602941607783, 38074553021241310, 37267602941607783, 34205488014964692,
    34205487625336413, 29777027807824809, 30587438473771711, 29777027807824809, 34133463533702408, 34133463159344445,
    0, 0, 0
  ]

abbrev PositiveTerm := Fin 7
abbrev NegativeTerm := Fin 57
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
noncomputable def positiveFloor : ℝ := 228243395009 / 1000000000000
noncomputable def negativeCeiling : ℝ := 56012347 / 10000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3816536525739919467899636416512, coefficient := (-3816536525739919467899636416512) }, { argument := 107433920442598371092651311104, coefficient := (-107433920442598371092651311104) }, { argument := 227987394483896227686455967744, coefficient := (-227987394483896227686455967744) }, { argument := 806395223280360245888674693120, coefficient := (-806395223280360245888674693120) }, { argument := 227987394483896227686455967744, coefficient := (-227987394483896227686455967744) }, { argument := 4667449961983596125786996736, coefficient := (-4667449961983596125786996736) }, { argument := 167647990186009475557714034688, coefficient := (-167647990186009475557714034688) }, { argument := 167648011962390854571839717376, coefficient := (-167648011962390854571839717376) }, { argument := 4667449138797641836498255872, coefficient := (-4667449138797641836498255872) }, { argument := 183358605755245234735061925888, coefficient := (-183358605755245234735061925888) }, { argument := 643964116500453354651034583040, coefficient := (-643964116500453354651034583040) }, { argument := 183358605755245234735061925888, coefficient := (-183358605755245234735061925888) }, { argument := 86907270596028777166241005568, coefficient := (-86907270596028777166241005568) }, { argument := 86907248044884147056314155008, coefficient := (-86907248044884147056314155008) }, { argument := 317513275553873758536073216, coefficient := (-317513275553873758536073216) }, { argument := 38692187169606711045496242176, coefficient := (-38692187169606711045496242176) }, { argument := 1449804289172844037766381568, coefficient := (-1449804289172844037766381568) }, { argument := 389860540873340616758760833024, coefficient := (-389860540873340616758760833024) }, { argument := 1101973663510597449906388992, coefficient := (-1101973663510597449906388992) }, { argument := 51851583981908704446382080, coefficient := (-51851583981908704446382080) }, { argument := 1449804289172844037766381568, coefficient := (-1449804289172844037766381568) }, { argument := 1158075377327088835045097472, coefficient := (-1158075377327088835045097472) }, { argument := 1101973663510597449906388992, coefficient := (-1101973663510597449906388992) }, { argument := 20379542562017337226932781056, coefficient := (-20379542562017337226932781056) }, { argument := 1189356332909617364940619776, coefficient := (-1189356332909617364940619776) }, { argument := 38692192884638327906659991552, coefficient := (-38692192884638327906659991552) }, { argument := 1449804289172844037766381568, coefficient := (-1449804289172844037766381568) }, { argument := 51851583981908704446382080, coefficient := (-51851583981908704446382080) }, { argument := 1189356332909617364940619776, coefficient := (-1189356332909617364940619776) }, { argument := 51851583981908704446382080, coefficient := (-51851583981908704446382080) }, { argument := 1454224424200810025686401024, coefficient := (-1454224424200810025686401024) }, { argument := 1158075377327088835045097472, coefficient := (-1158075377327088835045097472) }, { argument := 321755289925008865684881408, coefficient := (-321755289925008865684881408) }, { argument := 21537325095311931085871382528, coefficient := (-21537325095311931085871382528) }, { argument := 790892873743389100535244128256, coefficient := (-790892873743389100535244128256) }, { argument := 790867211857849598965318680576, coefficient := (-790867211857849598965318680576) }, { argument := 21563011157615384261377916928, coefficient := (-21563011157615384261377916928) }, { argument := 131117326766424676137059745792, coefficient := (-131117326766424676137059745792) }, { argument := 450804556993484385478521126912, coefficient := (-450804556993484385478521126912) }, { argument := 131117326766424676137059745792, coefficient := (-131117326766424676137059745792) }, { argument := 5242450423909284581407195136, coefficient := (-5242450423909284581407195136) }, { argument := 187914868705194309486865547264, coefficient := (-187914868705194309486865547264) }, { argument := 187914898406758111168457342976, coefficient := (-187914898406758111168457342976) }, { argument := 5242445973632276798977867776, coefficient := (-5242445973632276798977867776) }, { argument := 190750678650770771306958815232, coefficient := (-190750678650770771306958815232) }, { argument := 667440055048566065628341862400, coefficient := (-667440055048566065628341862400) }, { argument := 190750678650770771306958815232, coefficient := (-190750678650770771306958815232) }, { argument := 91356118672898396767458951168, coefficient := (-91356118672898396767458951168) }, { argument := 91356094000378198180933664768, coefficient := (-91356094000378198180933664768) }, { argument := 8485321043869241583870148608, coefficient := (-8485321043869241583870148608) }, { argument := 29761594395284622209701642240, coefficient := (-29761594395284622209701642240) }, { argument := 8485321043869241583870148608, coefficient := (-8485321043869241583870148608) }, { argument := 86907270596028777166241005568, coefficient := (-86907270596028777166241005568) }, { argument := 86907248044884147056314155008, coefficient := (-86907248044884147056314155008) }, { argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }, { argument := 1349017923130378876205272842371072, coefficient := 1349017923130378876205272842371072 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 48569803728837341722995326976, coefficient := 48569803728837341722995326976 }] }

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

end TermShard8


end Parent0

namespace Parent0

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3924144317888131415752375762157568)
def positiveArguments : Array ℕ := #[
    30051, 44955, 13041, 2511, 52083, 26163,
    2511, 30051, 2511, 21375, 16625, 2375,
    22325, 263625, 18525, 16625, 263625, 2375,
    18525, 18525, 18525, 18525, 18525, 21375,
    22325, 765, 3213, 13923, 459, 459,
    1071, 13923, 13923, 459, 171819, 6885,
    3213, 13923, 1071, 6885, 1071, 13923,
    13923, 459, 1, 37748741, 37748731, 1143008013,
    1985942771, 1143008013, 1394905119, 25684719363, 25683798875, 1396747045,
    204758817, 27339317175, 23409
  ]
def positiveCoefficients : Array ℕ := #[
    1162541753767655082531049439232, 869556163532410472782658273280, 1008998503270040260309967437824, 48569803728837341722995326976, 1007431735407819700899548233728, 1012132038994481379130805846016,
    48569803728837341722995326976, 1162541753767655082531049439232, 48569803728837341722995326976, 413452630308203177749512192000, 321574268017491360471842816000, 367513449162847269110677504000,
    431828302766345541205046067200, 5099249107134505858910650368000, 11466419613880834796253138124800, 321574268017491360471842816000, 5099249107134505858910650368000, 367513449162847269110677504000,
    358325612933776087382910566400, 358325612933776087382910566400, 358325612933776087382910566400, 11466419613880834796253138124800, 358325612933776087382910566400, 413452630308203177749512192000,
    431828302766345541205046067200, 29594504064166122196807188480, 497187668277990852906360766464, 1077239947935646847963781660672, 35513404876999346636168626176, 568214478031989546178698018816,
    41432305689832571075530063872, 1077239947935646847963781660672, 1077239947935646847963781660672, 568214478031989546178698018816, 13293851225623422090805789065216, 1065402146309980399085058785280,
    497187668277990852906360766464, 1077239947935646847963781660672, 41432305689832571075530063872, 1065402146309980399085058785280, 41432305689832571075530063872, 1077239947935646847963781660672,
    1077239947935646847963781660672, 35513404876999346636168626176, 158456325028528675187087900672, 713053557075708695734799826944, 713053368181049380948991279104, 5397702730242631713721625346048,
    18756699157335334494948642783232, 5397702730242631713721625346048, 6587253180748893918298399309824, 242585315683488368450315847991296, 242576621920130201022348918784000, 6595951430355220072428281528320,
    966946174472839319166105157632, 129106275091762434676955598028800, 905591824363483339222299967488
  ]
def positiveScales : Array ℕ := #[
    14, 15, 13, 11, 15, 14,
    11, 14, 11, 14, 14, 11,
    14, 18, 14, 14, 18, 11,
    14, 14, 14, 14, 14, 14,
    14, 9, 11, 13, 8, 8,
    10, 13, 13, 8, 17, 12,
    11, 13, 10, 12, 10, 13,
    13, 8, 0, 25, 25, 30,
    30, 30, 30, 34, 34, 30,
    27, 34, 14
  ]
def negativeArguments : Array ℕ := #[
    81, 475, 153, 1, 9, 373,
    3145
  ]
def negativeCoefficients : Array ℕ := #[
    6417481163655411345077059977216, 37633377194275560356933376409600, 24243817729364887303624448802816, 158456325028528675187087900672, 1426106925256758076683791106048, 29552104617820597922391893475328,
    498345142214722683463391447613440
  ]
def negativeScales : Array ℕ := #[
    6, 8, 7, 0, 3, 8,
    11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14875125379333676, 15456193964122088, 13670766880997015, 11294046313271499, 15668524930210465, 14675240357576065,
    11294046313271499, 14875125379333676, 11294046313271499, 14383636799547984, 14021066720163276, 11213711798105672,
    14446372554895944, 18008127664455778, 14177185922080558, 14021066720163276, 18008127664455778, 11213711798105672,
    14177185922080558, 14177185922080558, 14177185922080558, 14177185922080558, 14177185922080558, 14383636799547984,
    14446372554895944, 9579315937579817, 11649705265470097, 13765182482871986, 8842350343321225, 8842350343321225,
    10064742764750255, 13765182482871986, 13765182482871986, 8842350343321225, 17390530055093252, 12749240939008607,
    11649705265470097, 13765182482871986, 10064742764750255, 12749240939008607, 10064742764750255, 13765182482871986,
    13765182482871986, 8842350343321225, 0, 25169925192534133, 25169924810350465, 30090188371514891,
    30887176903031042, 30090188371514891, 30377519847722813, 34580191259435067, 34580139555258327, 30379423622072470,
    27609350335352039, 34670258159608258, 14514775685385275
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6339850002884626, 8891783706984896, 7257387842692652, 0, 3169925001442313, 8543031820256313,
    11618844301776098
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
noncomputable def positiveFloor : ℝ := 284910996887 / 1000000000000
noncomputable def negativeCeiling : ℝ := 79425836533 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1162541753767655082531049439232, coefficient := 1162541753767655082531049439232 }, { argument := 869556163532410472782658273280, coefficient := 869556163532410472782658273280 }, { argument := 1008998503270040260309967437824, coefficient := 1008998503270040260309967437824 }, { argument := 48569803728837341722995326976, coefficient := 48569803728837341722995326976 }, { argument := 1007431735407819700899548233728, coefficient := 1007431735407819700899548233728 }, { argument := 1012132038994481379130805846016, coefficient := 1012132038994481379130805846016 }, { argument := 48569803728837341722995326976, coefficient := 48569803728837341722995326976 }, { argument := 1162541753767655082531049439232, coefficient := 1162541753767655082531049439232 }, { argument := 48569803728837341722995326976, coefficient := 48569803728837341722995326976 }, { argument := 6417481163655411345077059977216, coefficient := (-6417481163655411345077059977216) }, { argument := 413452630308203177749512192000, coefficient := 413452630308203177749512192000 }, { argument := 321574268017491360471842816000, coefficient := 321574268017491360471842816000 }, { argument := 367513449162847269110677504000, coefficient := 367513449162847269110677504000 }, { argument := 431828302766345541205046067200, coefficient := 431828302766345541205046067200 }, { argument := 5099249107134505858910650368000, coefficient := 5099249107134505858910650368000 }, { argument := 11466419613880834796253138124800, coefficient := 11466419613880834796253138124800 }, { argument := 321574268017491360471842816000, coefficient := 321574268017491360471842816000 }, { argument := 5099249107134505858910650368000, coefficient := 5099249107134505858910650368000 }, { argument := 367513449162847269110677504000, coefficient := 367513449162847269110677504000 }, { argument := 358325612933776087382910566400, coefficient := 358325612933776087382910566400 }, { argument := 358325612933776087382910566400, coefficient := 358325612933776087382910566400 }, { argument := 358325612933776087382910566400, coefficient := 358325612933776087382910566400 }, { argument := 11466419613880834796253138124800, coefficient := 11466419613880834796253138124800 }, { argument := 358325612933776087382910566400, coefficient := 358325612933776087382910566400 }, { argument := 413452630308203177749512192000, coefficient := 413452630308203177749512192000 }, { argument := 431828302766345541205046067200, coefficient := 431828302766345541205046067200 }, { argument := 37633377194275560356933376409600, coefficient := (-37633377194275560356933376409600) }, { argument := 29594504064166122196807188480, coefficient := 29594504064166122196807188480 }, { argument := 497187668277990852906360766464, coefficient := 497187668277990852906360766464 }, { argument := 1077239947935646847963781660672, coefficient := 1077239947935646847963781660672 }, { argument := 35513404876999346636168626176, coefficient := 35513404876999346636168626176 }, { argument := 568214478031989546178698018816, coefficient := 568214478031989546178698018816 }, { argument := 41432305689832571075530063872, coefficient := 41432305689832571075530063872 }, { argument := 1077239947935646847963781660672, coefficient := 1077239947935646847963781660672 }, { argument := 1077239947935646847963781660672, coefficient := 1077239947935646847963781660672 }, { argument := 568214478031989546178698018816, coefficient := 568214478031989546178698018816 }, { argument := 13293851225623422090805789065216, coefficient := 13293851225623422090805789065216 }, { argument := 1065402146309980399085058785280, coefficient := 1065402146309980399085058785280 }, { argument := 497187668277990852906360766464, coefficient := 497187668277990852906360766464 }, { argument := 1077239947935646847963781660672, coefficient := 1077239947935646847963781660672 }, { argument := 41432305689832571075530063872, coefficient := 41432305689832571075530063872 }, { argument := 1065402146309980399085058785280, coefficient := 1065402146309980399085058785280 }, { argument := 41432305689832571075530063872, coefficient := 41432305689832571075530063872 }, { argument := 1077239947935646847963781660672, coefficient := 1077239947935646847963781660672 }, { argument := 1077239947935646847963781660672, coefficient := 1077239947935646847963781660672 }, { argument := 35513404876999346636168626176, coefficient := 35513404876999346636168626176 }, { argument := 24243817729364887303624448802816, coefficient := (-24243817729364887303624448802816) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 713053557075708695734799826944, coefficient := 713053557075708695734799826944 }, { argument := 713053368181049380948991279104, coefficient := 713053368181049380948991279104 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 5397702730242631713721625346048, coefficient := 5397702730242631713721625346048 }, { argument := 18756699157335334494948642783232, coefficient := 18756699157335334494948642783232 }, { argument := 5397702730242631713721625346048, coefficient := 5397702730242631713721625346048 }, { argument := 29552104617820597922391893475328, coefficient := (-29552104617820597922391893475328) }, { argument := 6587253180748893918298399309824, coefficient := 6587253180748893918298399309824 }, { argument := 242585315683488368450315847991296, coefficient := 242585315683488368450315847991296 }, { argument := 242576621920130201022348918784000, coefficient := 242576621920130201022348918784000 }, { argument := 6595951430355220072428281528320, coefficient := 6595951430355220072428281528320 }, { argument := 498345142214722683463391447613440, coefficient := (-498345142214722683463391447613440) }, { argument := 966946174472839319166105157632, coefficient := 966946174472839319166105157632 }, { argument := 129106275091762434676955598028800, coefficient := 129106275091762434676955598028800 }, { argument := 905591824363483339222299967488, coefficient := 905591824363483339222299967488 }] }

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

end TermShard9


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
