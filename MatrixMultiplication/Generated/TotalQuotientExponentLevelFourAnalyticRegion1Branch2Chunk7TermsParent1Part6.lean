import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 6, for level-four region 1, branch 2,
parent chunk 7, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard12

/-! Directed signed-log shard 12.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-47972991829240441472109928274460672)
def positiveArguments : Array ℕ := #[
    155, 1035, 805, 115, 1081, 12765,
    897, 805, 12765, 115, 897, 897,
    897, 897, 897, 1035, 1081, 11,
    11, 223049443, 1523721337, 446098881, 1200416459, 1081,
    21725690597, 26749, 851, 21725139495, 437, 437,
    14789, 805, 26749, 14789, 1201520413, 851,
    805, 1081, 201733281, 22398333893, 179775, 114114724665,
    184475, 5875, 179775, 102225, 184475, 2879925,
    3525, 11199170703, 179775, 5875, 3525, 5875,
    90475, 102225, 100866053, 303183345
  ]
def positiveCoefficients : Array ℕ := #[
    5996272065288560706542632960, 40039623145636518266268549120, 31141929113272847540431093760, 35590776129454682903349821440, 41819161952109252411436040192, 493822018796183725283978772480,
    1110432215238986106584514428928, 31141929113272847540431093760, 493822018796183725283978772480, 35590776129454682903349821440, 34701006726218315830766075904, 34701006726218315830766075904,
    34701006726218315830766075904, 1110432215238986106584514428928, 34701006726218315830766075904, 40039623145636518266268549120, 41819161952109252411436040192, 435754893828453856764491726848,
    435754893828453856764491726848, 4213284854583773626090035085312, 14391141142164246803457039663104, 4213284807360108797393582948352, 5668806451466663666011250622464, 41819161952109252411436040192,
    205193346184938025191842485633024, 1034801815963894905414896058368, 32921467919745581685598584832, 205188141173711140337409369047040, 33811237322981948758182330368, 33811237322981948758182330368,
    572121726280984027671348379648, 31141929113272847540431093760, 1034801815963894905414896058368, 572121726280984027671348379648, 5674019726834893542323491176448, 32921467919745581685598584832,
    31141929113272847540431093760, 41819161952109252411436040192, 952658484673723824264840216576, 105773141248426378290812344598528, 3477354227539519358124844646400, 1077783101919788005294308254023680,
    3568265449174539472062749081600, 113639027043775142422380544000, 3477354227539519358124844646400, 1977319070561687478149421465600, 3568265449174539472062749081600, 55705851056858574815450942668800,
    2181869319240482734509706444800, 105773176727565764090456835096576, 3477354227539519358124844646400, 113639027043775142422380544000, 2181869319240482734509706444800, 113639027043775142422380544000,
    3500082032948274386609320755200, 1977319070561687478149421465600, 952652935893106452431714123776, 2863485733184608469703186186240
  ]
def positiveScales : Array ℕ := #[
    7, 10, 9, 6, 10, 13,
    9, 9, 13, 6, 9, 9,
    9, 9, 9, 10, 10, 3,
    3, 27, 30, 28, 30, 10,
    34, 14, 9, 34, 8, 8,
    13, 9, 14, 13, 30, 9,
    9, 10, 27, 34, 17, 36,
    17, 12, 17, 16, 17, 21,
    11, 33, 17, 12, 11, 12,
    16, 16, 26, 28
  ]
def negativeArguments : Array ℕ := #[
    5, 23, 11, 9, 5367, 543
  ]
def negativeCoefficients : Array ℕ := #[
    792281625142643375935439503360, 3644495475656159529303021715456, 871509787656907713528983453696, 22817710804108129226940657696768, 425217548214056699864550381453312, 1376668551847857130025419681038336
  ]
def negativeScales : Array ℕ := #[
    2, 4, 3, 3, 12, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7276124405274237, 10015415052386687, 9652844973000555, 6845490050846035, 10078150807734650, 13639905917293458,
    9808964174871270, 9652844973000555, 13639905917293458, 6845490050846035, 9808964174871270, 9808964174871270,
    9808964174871270, 9808964174871270, 9808964174871270, 10015415052386687, 10078150807734650, 3459431618637292,
    3459431618637292, 27732788304501273, 30504951936287416, 28732788288331146, 30160887859070496, 10078150807734650,
    34338682985753662, 14707197337524912, 9733015321676379, 34338646389347067, 8771489469478456, 8771489469478456,
    13852236883273101, 9652844973000555, 14707197337524912, 13852236883273101, 30162214013052211, 9733015321676379,
    9652844973000555, 10078150807734650, 27587873871670491, 34382672369830445, 17455832884145009, 36731694003919635,
    17493065790343975, 12520373136339691, 17455832884145009, 16641388537300027, 17493065790343975, 21457599810319197,
    11783407542145078, 33382672853748850, 17455832884145009, 12520373136339691, 11783407542145078, 12520373136339691,
    16465231582147257, 16641388537300027, 26587865468636537, 28175615262126800
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2321928094887363, 4523561956057598, 3459431618637364, 3169925001442313, 12389900172773069, 9084808387804362
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
noncomputable def positiveFloor : ℝ := 767634502239 / 1000000000000
noncomputable def negativeCeiling : ℝ := 215088386587 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5996272065288560706542632960, coefficient := 5996272065288560706542632960 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 40039623145636518266268549120, coefficient := 40039623145636518266268549120 }, { argument := 31141929113272847540431093760, coefficient := 31141929113272847540431093760 }, { argument := 35590776129454682903349821440, coefficient := 35590776129454682903349821440 }, { argument := 41819161952109252411436040192, coefficient := 41819161952109252411436040192 }, { argument := 493822018796183725283978772480, coefficient := 493822018796183725283978772480 }, { argument := 1110432215238986106584514428928, coefficient := 1110432215238986106584514428928 }, { argument := 31141929113272847540431093760, coefficient := 31141929113272847540431093760 }, { argument := 493822018796183725283978772480, coefficient := 493822018796183725283978772480 }, { argument := 35590776129454682903349821440, coefficient := 35590776129454682903349821440 }, { argument := 34701006726218315830766075904, coefficient := 34701006726218315830766075904 }, { argument := 34701006726218315830766075904, coefficient := 34701006726218315830766075904 }, { argument := 34701006726218315830766075904, coefficient := 34701006726218315830766075904 }, { argument := 1110432215238986106584514428928, coefficient := 1110432215238986106584514428928 }, { argument := 34701006726218315830766075904, coefficient := 34701006726218315830766075904 }, { argument := 40039623145636518266268549120, coefficient := 40039623145636518266268549120 }, { argument := 41819161952109252411436040192, coefficient := 41819161952109252411436040192 }, { argument := 3644495475656159529303021715456, coefficient := (-3644495475656159529303021715456) }, { argument := 435754893828453856764491726848, coefficient := 435754893828453856764491726848 }, { argument := 435754893828453856764491726848, coefficient := 435754893828453856764491726848 }, { argument := 871509787656907713528983453696, coefficient := (-871509787656907713528983453696) }, { argument := 4213284854583773626090035085312, coefficient := 4213284854583773626090035085312 }, { argument := 14391141142164246803457039663104, coefficient := 14391141142164246803457039663104 }, { argument := 4213284807360108797393582948352, coefficient := 4213284807360108797393582948352 }, { argument := 22817710804108129226940657696768, coefficient := (-22817710804108129226940657696768) }, { argument := 5668806451466663666011250622464, coefficient := 5668806451466663666011250622464 }, { argument := 41819161952109252411436040192, coefficient := 41819161952109252411436040192 }, { argument := 205193346184938025191842485633024, coefficient := 205193346184938025191842485633024 }, { argument := 1034801815963894905414896058368, coefficient := 1034801815963894905414896058368 }, { argument := 32921467919745581685598584832, coefficient := 32921467919745581685598584832 }, { argument := 205188141173711140337409369047040, coefficient := 205188141173711140337409369047040 }, { argument := 33811237322981948758182330368, coefficient := 33811237322981948758182330368 }, { argument := 33811237322981948758182330368, coefficient := 33811237322981948758182330368 }, { argument := 572121726280984027671348379648, coefficient := 572121726280984027671348379648 }, { argument := 31141929113272847540431093760, coefficient := 31141929113272847540431093760 }, { argument := 1034801815963894905414896058368, coefficient := 1034801815963894905414896058368 }, { argument := 572121726280984027671348379648, coefficient := 572121726280984027671348379648 }, { argument := 5674019726834893542323491176448, coefficient := 5674019726834893542323491176448 }, { argument := 32921467919745581685598584832, coefficient := 32921467919745581685598584832 }, { argument := 31141929113272847540431093760, coefficient := 31141929113272847540431093760 }, { argument := 41819161952109252411436040192, coefficient := 41819161952109252411436040192 }, { argument := 425217548214056699864550381453312, coefficient := (-425217548214056699864550381453312) }, { argument := 952658484673723824264840216576, coefficient := 952658484673723824264840216576 }, { argument := 105773141248426378290812344598528, coefficient := 105773141248426378290812344598528 }, { argument := 3477354227539519358124844646400, coefficient := 3477354227539519358124844646400 }, { argument := 1077783101919788005294308254023680, coefficient := 1077783101919788005294308254023680 }, { argument := 3568265449174539472062749081600, coefficient := 3568265449174539472062749081600 }, { argument := 113639027043775142422380544000, coefficient := 113639027043775142422380544000 }, { argument := 3477354227539519358124844646400, coefficient := 3477354227539519358124844646400 }, { argument := 1977319070561687478149421465600, coefficient := 1977319070561687478149421465600 }, { argument := 3568265449174539472062749081600, coefficient := 3568265449174539472062749081600 }, { argument := 55705851056858574815450942668800, coefficient := 55705851056858574815450942668800 }, { argument := 2181869319240482734509706444800, coefficient := 2181869319240482734509706444800 }, { argument := 105773176727565764090456835096576, coefficient := 105773176727565764090456835096576 }, { argument := 3477354227539519358124844646400, coefficient := 3477354227539519358124844646400 }, { argument := 113639027043775142422380544000, coefficient := 113639027043775142422380544000 }, { argument := 2181869319240482734509706444800, coefficient := 2181869319240482734509706444800 }, { argument := 113639027043775142422380544000, coefficient := 113639027043775142422380544000 }, { argument := 3500082032948274386609320755200, coefficient := 3500082032948274386609320755200 }, { argument := 1977319070561687478149421465600, coefficient := 1977319070561687478149421465600 }, { argument := 952652935893106452431714123776, coefficient := 952652935893106452431714123776 }, { argument := 1376668551847857130025419681038336, coefficient := (-1376668551847857130025419681038336) }, { argument := 2863485733184608469703186186240, coefficient := 2863485733184608469703186186240 }] }

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

end TermShard12


end Parent1

namespace Parent1

namespace TermShard13

/-! Directed signed-log shard 13.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-8531455251596545083119155147702272)
def positiveArguments : Array ℕ := #[
    14718597647, 31535, 27931, 1307351, 355895, 7359300369,
    1307351, 31535, 31535, 13515, 31535, 355895,
    13515, 151590127, 27931, 176458949, 83667, 1059412795,
    134769, 4175, 134769, 90013, 177142981, 83667,
    501, 4815, 4401, 4815, 4401
  ]
def positiveCoefficients : Array ℕ := #[
    139013224406073651700061515546624, 1219951223089514592779496325120, 1080528226164998639318982459392, 50575692134368162117801404792832, 13768020946295950404225744240640, 139013253599743248800208226615296,
    50575692134368162117801404792832, 1219951223089514592779496325120, 1219951223089514592779496325120, 1045672476933869650953853992960, 1219951223089514592779496325120, 13768020946295950404225744240640,
    1045672476933869650953853992960, 2863456539515011369556475117568, 1080528226164998639318982459392, 833303826360004098411676565504, 1618355144795154866562266038272, 10005870949262500913000103280640,
    2606811580538303347935626133504, 80756244750257228870372556800, 2606811580538303347935626133504, 1741104636815545854445232324608, 836534076150014387566491467776, 1618355144795154866562266038272,
    77525994960246939715557654528, 186271290286222063238727598080, 170255441027967455932220178432, 186271290286222063238727598080, 170255441027967455932220178432
  ]
def positiveScales : Array ℕ := #[
    33, 14, 14, 20, 18, 32,
    20, 14, 14, 13, 14, 18,
    13, 27, 14, 27, 16, 29,
    17, 12, 17, 16, 27, 16,
    8, 12, 12, 12, 12
  ]
def negativeArguments : Array ℕ := #[
    5321, 139, 9
  ]
def negativeCoefficients : Array ℕ := #[
    421573052738400540335247359737856, 22025429178965485851005218193408, 713053462628379038341895553024
  ]
def negativeScales : Array ℕ := #[
    12, 7, 3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    33776921170237134, 14944666312170518, 14769579606179150, 20318215099880282, 18441092138878001, 32776921473212323,
    20318215099880282, 14944666312170518, 14944666312170518, 13722273891414535, 14944666312170518, 18441092138878001,
    13722273891414535, 27175600553557952, 14769579606179150, 27394757356405750, 16352371085669260, 29980617690841257,
    17040129155751832, 12027560482248776, 17040129155751832, 16457845755226553, 27400339061263518, 16352371085669260,
    8968666792316714, 12233320082730821, 12103615656394545, 12233320082730821, 12103615656394545
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    12377481688182961, 7118941072723508, 3169925001442313
  ]

abbrev PositiveTerm := Fin 29
abbrev NegativeTerm := Fin 3
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
noncomputable def positiveFloor : ℝ := 151098054339 / 1000000000000
noncomputable def negativeCeiling : ℝ := 12944827081 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 139013224406073651700061515546624, coefficient := 139013224406073651700061515546624 }, { argument := 1219951223089514592779496325120, coefficient := 1219951223089514592779496325120 }, { argument := 1080528226164998639318982459392, coefficient := 1080528226164998639318982459392 }, { argument := 50575692134368162117801404792832, coefficient := 50575692134368162117801404792832 }, { argument := 13768020946295950404225744240640, coefficient := 13768020946295950404225744240640 }, { argument := 139013253599743248800208226615296, coefficient := 139013253599743248800208226615296 }, { argument := 50575692134368162117801404792832, coefficient := 50575692134368162117801404792832 }, { argument := 1219951223089514592779496325120, coefficient := 1219951223089514592779496325120 }, { argument := 1219951223089514592779496325120, coefficient := 1219951223089514592779496325120 }, { argument := 1045672476933869650953853992960, coefficient := 1045672476933869650953853992960 }, { argument := 1219951223089514592779496325120, coefficient := 1219951223089514592779496325120 }, { argument := 13768020946295950404225744240640, coefficient := 13768020946295950404225744240640 }, { argument := 1045672476933869650953853992960, coefficient := 1045672476933869650953853992960 }, { argument := 2863456539515011369556475117568, coefficient := 2863456539515011369556475117568 }, { argument := 1080528226164998639318982459392, coefficient := 1080528226164998639318982459392 }, { argument := 421573052738400540335247359737856, coefficient := (-421573052738400540335247359737856) }, { argument := 833303826360004098411676565504, coefficient := 833303826360004098411676565504 }, { argument := 1618355144795154866562266038272, coefficient := 1618355144795154866562266038272 }, { argument := 10005870949262500913000103280640, coefficient := 10005870949262500913000103280640 }, { argument := 2606811580538303347935626133504, coefficient := 2606811580538303347935626133504 }, { argument := 80756244750257228870372556800, coefficient := 80756244750257228870372556800 }, { argument := 2606811580538303347935626133504, coefficient := 2606811580538303347935626133504 }, { argument := 1741104636815545854445232324608, coefficient := 1741104636815545854445232324608 }, { argument := 836534076150014387566491467776, coefficient := 836534076150014387566491467776 }, { argument := 1618355144795154866562266038272, coefficient := 1618355144795154866562266038272 }, { argument := 77525994960246939715557654528, coefficient := 77525994960246939715557654528 }, { argument := 22025429178965485851005218193408, coefficient := (-22025429178965485851005218193408) }, { argument := 186271290286222063238727598080, coefficient := 186271290286222063238727598080 }, { argument := 170255441027967455932220178432, coefficient := 170255441027967455932220178432 }, { argument := 186271290286222063238727598080, coefficient := 186271290286222063238727598080 }, { argument := 170255441027967455932220178432, coefficient := 170255441027967455932220178432 }, { argument := 713053462628379038341895553024, coefficient := (-713053462628379038341895553024) }] }

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

end TermShard13


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
