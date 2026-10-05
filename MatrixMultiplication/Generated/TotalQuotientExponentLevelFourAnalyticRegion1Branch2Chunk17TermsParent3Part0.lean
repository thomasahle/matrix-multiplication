import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 17, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-59099736390200851264595487264604160)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    10902415, 1491917603, 10163, 7536349735, 5437, 195,
    10163, 10097, 5437, 125981, 2499, 745958817,
    10163, 195, 2499, 195, 2541, 10097,
    5563615, 1060898132705379, 513, 39307054535950237, 8073, 243,
    78610375406446427, 243, 243, 20817, 243, 8073,
    20817, 2125530014750885, 243, 243, 513, 46302787418777463,
    723293655, 40634475, 81743363244732817, 2196970615, 46302786783548775, 2196970615,
    2196970615, 723293655, 40634475, 723293655, 19783920093, 5786347371,
    1060535660192533, 1060535348223211, 40634475, 1111456185, 325075695, 513,
    513, 2684607, 1060897819213725, 513, 39307042757263459, 8073,
    243, 78610351850854565, 243, 243
  ]
def negativeCoefficients : Array ℕ := #[
    51485199178335263022477475840, 7045381683610421648677759090688, 196581009675895620840621867008, 71178810783495065491563735941120, 105166874899915821166039662592, 7543697114395286050166538240,
    196581009675895620840621867008, 195304384010382572432132145152, 105166874899915821166039662592, 2436826938893929568938540138496, 193350759885885331685806964736, 7045381830003782617636760715264,
    196581009675895620840621867008, 7543697114395286050166538240, 193350759885885331685806964736, 7543697114395286050166538240, 196600352489009454907417165824, 195304384010382572432132145152,
    52546857999181602311194542080, 4777860435129999879868445097984, 19845726254793752531976585216, 177023236161137251921113018007552, 156154530267982421238447341568, 18801214346646712925030449152,
    177014828693963465839634752208896, 18801214346646712925030449152, 18801214346646712925030449152, 805318681181367536955470905344, 18801214346646712925030449152, 156154530267982421238447341568,
    805318681181367536955470905344, 4786268091198445276132519444480, 18801214346646712925030449152, 18801214346646712925030449152, 19845726254793752531976585216, 52132304041355368172578418982912,
    13342412943922970996747796480, 749573760894548932401561600, 184069690124494906732289894383616, 20263477336182639472588881920, 52132303326151447529616152985600, 20263477336182639472588881920,
    20263477336182639472588881920, 13342412943922970996747796480, 749573760894548932401561600, 13342412943922970996747796480, 45618613841286383907725377536, 13342408634302386776353800192,
    4776228004056214586943883706368, 4776226599071292276717603782656, 749573760894548932401561600, 2562843474229572129647493120, 749573518781032964963696640, 19845726254793752531976585216,
    19845726254793752531976585216, 50710792465908918512819109888, 4777859023289103741707983257600, 19845726254793752531976585216, 177023183114647867606524875505664, 156154530267982421238447341568,
    18801214346646712925030449152, 177014775651486099742290733957120, 18801214346646712925030449152, 18801214346646712925030449152
  ]
def negativeScales : Array ℕ := #[
    23, 30, 13, 32, 12, 7,
    13, 13, 12, 16, 11, 29,
    13, 7, 11, 7, 11, 13,
    22, 49, 9, 55, 12, 7,
    56, 7, 7, 14, 7, 12,
    14, 50, 7, 7, 9, 55,
    29, 25, 56, 31, 55, 31,
    31, 29, 25, 29, 34, 32,
    49, 49, 25, 30, 28, 9,
    9, 21, 49, 9, 55, 12,
    7, 56, 7, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23378144406792810, 30474520713288736, 13311038711409478, 32811218771611013, 12408595112798111, 7607330313756529,
    13311038711409478, 13301639085592372, 12408595112798111, 16942846651738929, 11287135186086704, 29474520743265958,
    13311038711409478, 7607330313756529, 11287135186086704, 7607330313756529, 11311180660053356, 13301639085592372,
    22407591158721170, 49914207564453765, 9002815015607055, 55125637778027273, 12978889193202904, 7924812510375204,
    56125569257648227, 7924812510375204, 7924812510375204, 14345474552078504, 7924812510375204, 12978889193202904,
    14345474552078504, 50916744060702978, 7924812510375204, 7924812510375204, 9002815015607055, 55361948564257849,
    29430006254960454, 25276200918881397, 56181951120948074, 31032868427490151, 55361948544465492, 31032868427490151,
    31032868427490151, 29430006254960454, 25276200918881397, 29430006254960454, 34203609266699078, 32430005788967588,
    49913714560754872, 49913714136368667, 25276200918881397, 30049803930620043, 28276200452888531, 9002815015607055,
    9002815015607055, 21356279476659957, 49914207138142367, 9002815015607055, 55125637345711605, 12978889193202904,
    7924812510375204, 56125568825344724, 7924812510375204, 7924812510375204
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
noncomputable def negativeCeiling : ℝ := 44807908717 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 51485199178335263022477475840, coefficient := (-51485199178335263022477475840) }, { argument := 7045381683610421648677759090688, coefficient := (-7045381683610421648677759090688) }, { argument := 196581009675895620840621867008, coefficient := (-196581009675895620840621867008) }, { argument := 71178810783495065491563735941120, coefficient := (-71178810783495065491563735941120) }, { argument := 105166874899915821166039662592, coefficient := (-105166874899915821166039662592) }, { argument := 7543697114395286050166538240, coefficient := (-7543697114395286050166538240) }, { argument := 196581009675895620840621867008, coefficient := (-196581009675895620840621867008) }, { argument := 195304384010382572432132145152, coefficient := (-195304384010382572432132145152) }, { argument := 105166874899915821166039662592, coefficient := (-105166874899915821166039662592) }, { argument := 2436826938893929568938540138496, coefficient := (-2436826938893929568938540138496) }, { argument := 193350759885885331685806964736, coefficient := (-193350759885885331685806964736) }, { argument := 7045381830003782617636760715264, coefficient := (-7045381830003782617636760715264) }, { argument := 196581009675895620840621867008, coefficient := (-196581009675895620840621867008) }, { argument := 7543697114395286050166538240, coefficient := (-7543697114395286050166538240) }, { argument := 193350759885885331685806964736, coefficient := (-193350759885885331685806964736) }, { argument := 7543697114395286050166538240, coefficient := (-7543697114395286050166538240) }, { argument := 196600352489009454907417165824, coefficient := (-196600352489009454907417165824) }, { argument := 195304384010382572432132145152, coefficient := (-195304384010382572432132145152) }, { argument := 52546857999181602311194542080, coefficient := (-52546857999181602311194542080) }, { argument := 4777860435129999879868445097984, coefficient := (-4777860435129999879868445097984) }, { argument := 19845726254793752531976585216, coefficient := (-19845726254793752531976585216) }, { argument := 177023236161137251921113018007552, coefficient := (-177023236161137251921113018007552) }, { argument := 156154530267982421238447341568, coefficient := (-156154530267982421238447341568) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 177014828693963465839634752208896, coefficient := (-177014828693963465839634752208896) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 805318681181367536955470905344, coefficient := (-805318681181367536955470905344) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 156154530267982421238447341568, coefficient := (-156154530267982421238447341568) }, { argument := 805318681181367536955470905344, coefficient := (-805318681181367536955470905344) }, { argument := 4786268091198445276132519444480, coefficient := (-4786268091198445276132519444480) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 19845726254793752531976585216, coefficient := (-19845726254793752531976585216) }, { argument := 52132304041355368172578418982912, coefficient := (-52132304041355368172578418982912) }, { argument := 13342412943922970996747796480, coefficient := (-13342412943922970996747796480) }, { argument := 749573760894548932401561600, coefficient := (-749573760894548932401561600) }, { argument := 184069690124494906732289894383616, coefficient := (-184069690124494906732289894383616) }, { argument := 20263477336182639472588881920, coefficient := (-20263477336182639472588881920) }, { argument := 52132303326151447529616152985600, coefficient := (-52132303326151447529616152985600) }, { argument := 20263477336182639472588881920, coefficient := (-20263477336182639472588881920) }, { argument := 20263477336182639472588881920, coefficient := (-20263477336182639472588881920) }, { argument := 13342412943922970996747796480, coefficient := (-13342412943922970996747796480) }, { argument := 749573760894548932401561600, coefficient := (-749573760894548932401561600) }, { argument := 13342412943922970996747796480, coefficient := (-13342412943922970996747796480) }, { argument := 45618613841286383907725377536, coefficient := (-45618613841286383907725377536) }, { argument := 13342408634302386776353800192, coefficient := (-13342408634302386776353800192) }, { argument := 4776228004056214586943883706368, coefficient := (-4776228004056214586943883706368) }, { argument := 4776226599071292276717603782656, coefficient := (-4776226599071292276717603782656) }, { argument := 749573760894548932401561600, coefficient := (-749573760894548932401561600) }, { argument := 2562843474229572129647493120, coefficient := (-2562843474229572129647493120) }, { argument := 749573518781032964963696640, coefficient := (-749573518781032964963696640) }, { argument := 19845726254793752531976585216, coefficient := (-19845726254793752531976585216) }, { argument := 19845726254793752531976585216, coefficient := (-19845726254793752531976585216) }, { argument := 50710792465908918512819109888, coefficient := (-50710792465908918512819109888) }, { argument := 4777859023289103741707983257600, coefficient := (-4777859023289103741707983257600) }, { argument := 19845726254793752531976585216, coefficient := (-19845726254793752531976585216) }, { argument := 177023183114647867606524875505664, coefficient := (-177023183114647867606524875505664) }, { argument := 156154530267982421238447341568, coefficient := (-156154530267982421238447341568) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 177014775651486099742290733957120, coefficient := (-177014775651486099742290733957120) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }] }

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


end Parent3

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-109425447890165075303534703558000640)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    20817, 243, 8073, 20817, 2125529385985883, 243,
    243, 513, 163502677545928013, 19783920093, 1111456185, 288414113931463843,
    60092731069, 163502675389998445, 60092731069, 60092731069, 19783920093, 1111456185,
    39289824793058539, 39289813071569685, 2196970615, 60092731069, 17575759243, 8073,
    8073, 368026079, 243, 243, 9799, 11575696698805455,
    5786347371, 325075695, 20435840546638067, 17575759243, 11575696539998283, 17575759243,
    17575759243, 5786347371, 325075695, 78575934130238173, 78575910689033507, 14876265661,
    243, 243, 5245, 47, 2196970615, 60092731069,
    17575759243, 243, 243, 2196970615, 60092731069, 17575759243,
    20817, 20817, 9799, 243, 243, 9733,
    723293655, 19783920093, 5786347371, 8073
  ]
def negativeCoefficients : Array ℕ := #[
    805318681181367536955470905344, 18801214346646712925030449152, 156154530267982421238447341568, 805318681181367536955470905344, 4786266675345530920727933353984, 18801214346646712925030449152,
    18801214346646712925030449152, 19845726254793752531976585216, 184087649417479940683926824026112, 45618613841286383907725377536, 2562843474229572129647493120, 649450848015066171226969094488064,
    69282201920006099904803897344, 184087646990119040913468219719680, 69282201920006099904803897344, 69282201920006099904803897344, 45618613841286383907725377536, 2562843474229572129647493120,
    176945640297470511356093969465344, 176945587508577676254271777013760, 20263477336182639472588881920, 69282201920006099904803897344, 20263470791047257819518599168, 156154530267982421238447341568,
    156154530267982421238447341568, 6951816081166144784470623911936, 18801214346646712925030449152, 18801214346646712925030449152, 189540225702460020527133097984, 52132303339294127807685910855680,
    13342408634302386776353800192, 749573518781032964963696640, 184069687741684143648736452542464, 20263470791047257819518599168, 52132302624090207164723644858368, 20263470791047257819518599168,
    20263470791047257819518599168, 13342408634302386776353800192, 749573518781032964963696640, 176937273834614637317739096571904, 176937221049714337861173023604736, 70251178347771047831758811693056,
    18801214346646712925030449152, 18801214346646712925030449152, 101453054782059680341342289920, 7272897730801609115032354816, 20263477336182639472588881920, 69282201920006099904803897344,
    20263470791047257819518599168, 18801214346646712925030449152, 18801214346646712925030449152, 20263477336182639472588881920, 69282201920006099904803897344, 20263470791047257819518599168,
    805318681181367536955470905344, 805318681181367536955470905344, 189540225702460020527133097984, 18801214346646712925030449152, 18801214346646712925030449152, 188263600036946972118643376128,
    13342412943922970996747796480, 45618613841286383907725377536, 13342408634302386776353800192, 156154530267982421238447341568
  ]
def negativeScales : Array ℕ := #[
    14, 7, 12, 14, 50, 7,
    7, 9, 57, 34, 30, 58,
    35, 57, 35, 35, 34, 30,
    55, 55, 31, 35, 34, 12,
    12, 28, 7, 7, 13, 53,
    32, 28, 54, 34, 53, 34,
    34, 32, 28, 56, 56, 33,
    7, 7, 12, 5, 31, 35,
    34, 7, 7, 31, 35, 34,
    14, 14, 13, 7, 7, 13,
    29, 34, 32, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    14345474552078504, 7924812510375204, 12978889193202904, 14345474552078504, 50916743633931127, 7924812510375204,
    7924812510375204, 9002815015607055, 57182091874806086, 34203609266699078, 30049803930620043, 58000919379608067,
    35806471439965521, 57182091855782857, 35806471439965521, 35806471439965521, 34203609266699078, 30049803930620043,
    55125005252531706, 55125004822126723, 31032868427490151, 35806471439965521, 34032867961497285, 12978889193202904,
    12978889193202904, 28455232761008651, 7924812510375204, 7924812510375204, 13258418812598833, 53361948544829199,
    32430005788967588, 28276200452888531, 54181951102272163, 34032867961497285, 53361948525036842, 34032867961497285,
    34032867961497285, 32430005788967588, 28276200452888531, 56124937036441060, 56124936606048280, 33792293366428723,
    7924812510375204, 7924812510375204, 12356727057464632, 5554588851679165, 31032868427490151, 35806471439965521,
    34032867961497285, 7924812510375204, 7924812510375204, 31032868427490151, 35806471439965521, 34032867961497285,
    14345474552078504, 14345474552078504, 13258418812598833, 7924812510375204, 7924812510375204, 13248668839723137,
    29430006254960454, 34203609266699078, 32430005788967588, 12978889193202904
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
noncomputable def negativeCeiling : ℝ := 701376308307 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 805318681181367536955470905344, coefficient := (-805318681181367536955470905344) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 156154530267982421238447341568, coefficient := (-156154530267982421238447341568) }, { argument := 805318681181367536955470905344, coefficient := (-805318681181367536955470905344) }, { argument := 4786266675345530920727933353984, coefficient := (-4786266675345530920727933353984) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 19845726254793752531976585216, coefficient := (-19845726254793752531976585216) }, { argument := 184087649417479940683926824026112, coefficient := (-184087649417479940683926824026112) }, { argument := 45618613841286383907725377536, coefficient := (-45618613841286383907725377536) }, { argument := 2562843474229572129647493120, coefficient := (-2562843474229572129647493120) }, { argument := 649450848015066171226969094488064, coefficient := (-649450848015066171226969094488064) }, { argument := 69282201920006099904803897344, coefficient := (-69282201920006099904803897344) }, { argument := 184087646990119040913468219719680, coefficient := (-184087646990119040913468219719680) }, { argument := 69282201920006099904803897344, coefficient := (-69282201920006099904803897344) }, { argument := 69282201920006099904803897344, coefficient := (-69282201920006099904803897344) }, { argument := 45618613841286383907725377536, coefficient := (-45618613841286383907725377536) }, { argument := 2562843474229572129647493120, coefficient := (-2562843474229572129647493120) }, { argument := 176945640297470511356093969465344, coefficient := (-176945640297470511356093969465344) }, { argument := 176945587508577676254271777013760, coefficient := (-176945587508577676254271777013760) }, { argument := 20263477336182639472588881920, coefficient := (-20263477336182639472588881920) }, { argument := 69282201920006099904803897344, coefficient := (-69282201920006099904803897344) }, { argument := 20263470791047257819518599168, coefficient := (-20263470791047257819518599168) }, { argument := 156154530267982421238447341568, coefficient := (-156154530267982421238447341568) }, { argument := 156154530267982421238447341568, coefficient := (-156154530267982421238447341568) }, { argument := 6951816081166144784470623911936, coefficient := (-6951816081166144784470623911936) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 189540225702460020527133097984, coefficient := (-189540225702460020527133097984) }, { argument := 52132303339294127807685910855680, coefficient := (-52132303339294127807685910855680) }, { argument := 13342408634302386776353800192, coefficient := (-13342408634302386776353800192) }, { argument := 749573518781032964963696640, coefficient := (-749573518781032964963696640) }, { argument := 184069687741684143648736452542464, coefficient := (-184069687741684143648736452542464) }, { argument := 20263470791047257819518599168, coefficient := (-20263470791047257819518599168) }, { argument := 52132302624090207164723644858368, coefficient := (-52132302624090207164723644858368) }, { argument := 20263470791047257819518599168, coefficient := (-20263470791047257819518599168) }, { argument := 20263470791047257819518599168, coefficient := (-20263470791047257819518599168) }, { argument := 13342408634302386776353800192, coefficient := (-13342408634302386776353800192) }, { argument := 749573518781032964963696640, coefficient := (-749573518781032964963696640) }, { argument := 176937273834614637317739096571904, coefficient := (-176937273834614637317739096571904) }, { argument := 176937221049714337861173023604736, coefficient := (-176937221049714337861173023604736) }, { argument := 70251178347771047831758811693056, coefficient := (-70251178347771047831758811693056) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 101453054782059680341342289920, coefficient := (-101453054782059680341342289920) }, { argument := 7272897730801609115032354816, coefficient := (-7272897730801609115032354816) }, { argument := 20263477336182639472588881920, coefficient := (-20263477336182639472588881920) }, { argument := 69282201920006099904803897344, coefficient := (-69282201920006099904803897344) }, { argument := 20263470791047257819518599168, coefficient := (-20263470791047257819518599168) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 20263477336182639472588881920, coefficient := (-20263477336182639472588881920) }, { argument := 69282201920006099904803897344, coefficient := (-69282201920006099904803897344) }, { argument := 20263470791047257819518599168, coefficient := (-20263470791047257819518599168) }, { argument := 805318681181367536955470905344, coefficient := (-805318681181367536955470905344) }, { argument := 805318681181367536955470905344, coefficient := (-805318681181367536955470905344) }, { argument := 189540225702460020527133097984, coefficient := (-189540225702460020527133097984) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 18801214346646712925030449152, coefficient := (-18801214346646712925030449152) }, { argument := 188263600036946972118643376128, coefficient := (-188263600036946972118643376128) }, { argument := 13342412943922970996747796480, coefficient := (-13342412943922970996747796480) }, { argument := 45618613841286383907725377536, coefficient := (-45618613841286383907725377536) }, { argument := 13342408634302386776353800192, coefficient := (-13342408634302386776353800192) }, { argument := 156154530267982421238447341568, coefficient := (-156154530267982421238447341568) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17
