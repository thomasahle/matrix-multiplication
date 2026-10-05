import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-5691090107570058785875393849065472)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    17863272303, 8244662553101, 38295, 29785, 4255, 39997,
    472305, 33189, 29785, 472305, 4255, 33189,
    33189, 33189, 33189, 33189, 38295, 39997,
    49277781, 7867059417, 314005689963, 7867059417, 197088633, 4275069258593,
    48645, 309286255586613, 1203705, 38295, 2474210783555223, 19665,
    19665, 665505, 36225, 1203705, 665505, 68480455242161,
    38295, 36225, 48645, 68579961603215, 70723224985, 413689516364145,
    54826616635, 6964925645, 219290986745, 74908834345, 68845589333135, 70723224985,
    6705523565, 2478239286916897, 120295468105328863, 128898293415, 114187227123, 5341832104847,
    1456097614319, 60147746672543687, 5341832104847, 128898293415, 128896550567, 55246233891,
    128896550567, 1456097614319, 55246233891, 1239107023579193
  ]
def negativeCoefficients : Array ℕ := #[
    82379803123106305962160422912, 37130659201941145790600708096, 180843024461493063458488320, 140655685692272382689935360, 160749355076882723074211840, 188880492215337199612198912,
    2230397301691747782654689280, 5015379878398740959915409408, 140655685692272382689935360, 2230397301691747782654689280, 160749355076882723074211840, 156730621199960654997356544,
    156730621199960654997356544, 156730621199960654997356544, 5015379878398740959915409408, 156730621199960654997356544, 180843024461493063458488320, 188880492215337199612198912,
    909014614627307142141444096, 145121631678065670163500367872, 1448095650109012271011360407552, 145121631678065670163500367872, 908910893197066691760095232, 19253200319982497404842672128,
    229719517559193891420241920, 696450732705343146771584385024, 5684336147262606291951943680, 180843024461493063458488320, 696428422678460327197868556288, 185730673771263146254663680,
    185730673771263146254663680, 3142758506182163237940756480, 171067725841952897866137600, 5684336147262606291951943680, 3142758506182163237940756480, 19275534544422388063709167616,
    180843024461493063458488320, 171067725841952897866137600, 229719517559193891420241920, 77214172380330499363737436160, 163076653920709505310229790720, 931545975872322064614382632960,
    252843141373307942197044183040, 8030012554108214145733099520, 252825294384765536650259333120, 172728012002764908955896381440, 77513242616702245051553546240, 163076653920709505310229790720,
    7730942317736468457916989440, 697562345568366315752686354432, 33860164083344903366892876464128, 297219228770553271460906926080, 263297819403065852938835460096, 12317426215354727178028233785344,
    3357532504710203699572598898688, 33860171187705342433199436857344, 12317426215354727178028233785344, 297219228770553271460906926080, 297215210036676349392830070784, 254778284405894008144568254464,
    297215210036676349392830070784, 3357532504710203699572598898688, 254778284405894008144568254464, 697555241207927249446125961216
  ]
def negativeScales : Array ℕ := #[
    34, 42, 15, 14, 12, 15,
    18, 15, 14, 18, 12, 15,
    15, 15, 15, 15, 15, 15,
    25, 32, 38, 32, 27, 41,
    15, 48, 20, 15, 51, 14,
    14, 19, 15, 20, 19, 45,
    15, 15, 15, 45, 36, 48,
    35, 32, 37, 36, 45, 36,
    32, 51, 56, 36, 36, 42,
    40, 55, 42, 36, 36, 35,
    36, 40, 35, 50
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34056277335205052, 42906597590174384, 15224868418015638, 14862298340817341, 12054943416573326, 15287604173363601,
    18849359284634491, 15018417540548212, 14862298340817341, 18849359284634491, 12054943416573326, 15018417540548212,
    15018417540548212, 15018417540548212, 15018417540548212, 15018417540548212, 15224868418015638, 15287604173363601,
    25554433956520759, 32873177336453864, 38191999745575429, 32873177336453864, 27554269331080864, 41959084943472256,
    15570003904066736, 48135936051156366, 20199050433859907, 15224868418015638, 51135889835280388, 14263342565830274,
    14263342565830274, 19344089979714636, 15144698069331655, 20199050433859907, 19344089979714636, 45960757538494470,
    15224868418015638, 15144698069331655, 15570003904066736, 45962852342998015, 36041465012118010, 48555541725975697,
    35674157396201969, 32697460805278336, 37674055559662136, 36124416821284452, 45968429477226505, 36041465012118010,
    32642702835669823, 51138236917238313, 56739359906108542, 36907442211610582, 36732610325114775, 42280471771058825,
    40405244213260111, 55739360208807150, 42280471771058825, 36907442211610582, 36907422704638677, 35685157068958537,
    36907422704638677, 40405244213260111, 35685157068958537, 50138222223959880
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
noncomputable def negativeCeiling : ℝ := 21162063 / 320000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 82379803123106305962160422912, coefficient := (-82379803123106305962160422912) }, { argument := 37130659201941145790600708096, coefficient := (-37130659201941145790600708096) }, { argument := 180843024461493063458488320, coefficient := (-180843024461493063458488320) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 160749355076882723074211840, coefficient := (-160749355076882723074211840) }, { argument := 188880492215337199612198912, coefficient := (-188880492215337199612198912) }, { argument := 2230397301691747782654689280, coefficient := (-2230397301691747782654689280) }, { argument := 5015379878398740959915409408, coefficient := (-5015379878398740959915409408) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 2230397301691747782654689280, coefficient := (-2230397301691747782654689280) }, { argument := 160749355076882723074211840, coefficient := (-160749355076882723074211840) }, { argument := 156730621199960654997356544, coefficient := (-156730621199960654997356544) }, { argument := 156730621199960654997356544, coefficient := (-156730621199960654997356544) }, { argument := 156730621199960654997356544, coefficient := (-156730621199960654997356544) }, { argument := 5015379878398740959915409408, coefficient := (-5015379878398740959915409408) }, { argument := 156730621199960654997356544, coefficient := (-156730621199960654997356544) }, { argument := 180843024461493063458488320, coefficient := (-180843024461493063458488320) }, { argument := 188880492215337199612198912, coefficient := (-188880492215337199612198912) }, { argument := 909014614627307142141444096, coefficient := (-909014614627307142141444096) }, { argument := 145121631678065670163500367872, coefficient := (-145121631678065670163500367872) }, { argument := 1448095650109012271011360407552, coefficient := (-1448095650109012271011360407552) }, { argument := 145121631678065670163500367872, coefficient := (-145121631678065670163500367872) }, { argument := 908910893197066691760095232, coefficient := (-908910893197066691760095232) }, { argument := 19253200319982497404842672128, coefficient := (-19253200319982497404842672128) }, { argument := 229719517559193891420241920, coefficient := (-229719517559193891420241920) }, { argument := 696450732705343146771584385024, coefficient := (-696450732705343146771584385024) }, { argument := 5684336147262606291951943680, coefficient := (-5684336147262606291951943680) }, { argument := 180843024461493063458488320, coefficient := (-180843024461493063458488320) }, { argument := 696428422678460327197868556288, coefficient := (-696428422678460327197868556288) }, { argument := 185730673771263146254663680, coefficient := (-185730673771263146254663680) }, { argument := 185730673771263146254663680, coefficient := (-185730673771263146254663680) }, { argument := 3142758506182163237940756480, coefficient := (-3142758506182163237940756480) }, { argument := 171067725841952897866137600, coefficient := (-171067725841952897866137600) }, { argument := 5684336147262606291951943680, coefficient := (-5684336147262606291951943680) }, { argument := 3142758506182163237940756480, coefficient := (-3142758506182163237940756480) }, { argument := 19275534544422388063709167616, coefficient := (-19275534544422388063709167616) }, { argument := 180843024461493063458488320, coefficient := (-180843024461493063458488320) }, { argument := 171067725841952897866137600, coefficient := (-171067725841952897866137600) }, { argument := 229719517559193891420241920, coefficient := (-229719517559193891420241920) }, { argument := 77214172380330499363737436160, coefficient := (-77214172380330499363737436160) }, { argument := 163076653920709505310229790720, coefficient := (-163076653920709505310229790720) }, { argument := 931545975872322064614382632960, coefficient := (-931545975872322064614382632960) }, { argument := 252843141373307942197044183040, coefficient := (-252843141373307942197044183040) }, { argument := 8030012554108214145733099520, coefficient := (-8030012554108214145733099520) }, { argument := 252825294384765536650259333120, coefficient := (-252825294384765536650259333120) }, { argument := 172728012002764908955896381440, coefficient := (-172728012002764908955896381440) }, { argument := 77513242616702245051553546240, coefficient := (-77513242616702245051553546240) }, { argument := 163076653920709505310229790720, coefficient := (-163076653920709505310229790720) }, { argument := 7730942317736468457916989440, coefficient := (-7730942317736468457916989440) }, { argument := 697562345568366315752686354432, coefficient := (-697562345568366315752686354432) }, { argument := 33860164083344903366892876464128, coefficient := (-33860164083344903366892876464128) }, { argument := 297219228770553271460906926080, coefficient := (-297219228770553271460906926080) }, { argument := 263297819403065852938835460096, coefficient := (-263297819403065852938835460096) }, { argument := 12317426215354727178028233785344, coefficient := (-12317426215354727178028233785344) }, { argument := 3357532504710203699572598898688, coefficient := (-3357532504710203699572598898688) }, { argument := 33860171187705342433199436857344, coefficient := (-33860171187705342433199436857344) }, { argument := 12317426215354727178028233785344, coefficient := (-12317426215354727178028233785344) }, { argument := 297219228770553271460906926080, coefficient := (-297219228770553271460906926080) }, { argument := 297215210036676349392830070784, coefficient := (-297215210036676349392830070784) }, { argument := 254778284405894008144568254464, coefficient := (-254778284405894008144568254464) }, { argument := 297215210036676349392830070784, coefficient := (-297215210036676349392830070784) }, { argument := 3357532504710203699572598898688, coefficient := (-3357532504710203699572598898688) }, { argument := 254778284405894008144568254464, coefficient := (-254778284405894008144568254464) }, { argument := 697555241207927249446125961216, coefficient := (-697555241207927249446125961216) }] }

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


end Parent1

namespace Parent1

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-30962927210561125848311427743350784)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    114187227123, 84179644870131, 36559145383689715, 1253886666723, 373264514887498625, 1286668017487,
    40976688455, 1253886666723, 712994379117, 1286668017487, 20086772680641, 24586013073,
    9139789649345725, 1253886666723, 40976688455, 24586013073, 40976688455, 631041002207,
    712994379117, 84179644117491, 19665, 15295, 2185, 20539,
    242535, 17043, 15295, 242535, 2185, 17043,
    17043, 17043, 17043, 17043, 19665, 20539,
    50566089, 8072734173, 322214989047, 8072734173, 202241277, 208656768434335,
    37835, 14994666399333067, 936215, 29785, 119957296398004585, 15295,
    15295, 517615, 28175, 936215, 517615, 3338550320508495,
    29785, 28175, 37835, 1610385, 257093445, 10261623855,
    257093445, 6440805, 1759746255, 5405
  ]
def negativeCoefficients : Array ℕ := #[
    263297819403065852938835460096, 379111417269302656746941054976, 41161938381742197371452952412160, 1445632902404745243339572379648, 420258482539491941055192891392000, 1483427226650620935975901069312,
    47242905307344615795410862080, 1445632902404745243339572379648, 822026552347796314840149000192, 1483427226650620935975901069312, 23158472181660330662910404591616, 907063781901016623271888551936,
    41161953259038123409968568729600, 1445632902404745243339572379648, 47242905307344615795410862080, 907063781901016623271888551936, 47242905307344615795410862080, 1455081483466214166498654552064,
    822026552347796314840149000192, 379111413879713433202810945536, 185730673771263146254663680, 144457190710982447086960640, 165093932241122796670812160, 193985370383319286088204288,
    2290678309845578803807518720, 5150930685923031256129339392, 144457190710982447086960640, 2290678309845578803807518720, 165093932241122796670812160, 160966583935094726754041856,
    160966583935094726754041856, 160966583935094726754041856, 5150930685923031256129339392, 160966583935094726754041856, 185730673771263146254663680, 193985370383319286088204288,
    932779702591419747164749824, 148915661264420328206990573568, 1485954359915783833652180287488, 148915661264420328206990573568, 932673269489800461479313408, 939706544569202978070892380160,
    178670735879373026660188160, 33764987004290648756126656495616, 4421150336759804893740400640, 140655685692272382689935360, 33764977209901599439785306357760, 144457190710982447086960640,
    144457190710982447086960640, 2444367727030571407287255040, 133052675654852253895884800, 4421150336759804893740400640, 2444367727030571407287255040, 939718373712481754492405022720,
    140655685692272382689935360, 133052675654852253895884800, 178670735879373026660188160, 29706359955140756279132160, 4742536982943322554362757120, 47323387258464453301024849920,
    4742536982943322554362757120, 29702970365917212149022720, 8115397200163456853496299520, 204195126719283459040215040
  ]
def negativeScales : Array ℕ := #[
    36, 46, 55, 40, 58, 40,
    35, 40, 39, 40, 44, 34,
    53, 40, 35, 34, 35, 39,
    39, 46, 14, 13, 11, 14,
    17, 14, 13, 17, 11, 14,
    14, 14, 14, 14, 14, 14,
    25, 32, 38, 32, 27, 47,
    15, 53, 19, 14, 56, 13,
    13, 18, 14, 19, 18, 51,
    14, 14, 15, 20, 27, 33,
    27, 22, 30, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36732610325114775, 46258536656909362, 55021081864164801, 40189544093849117, 58372975975652768, 40226777000048092,
    35254084346043827, 40189544093849117, 39375099747005196, 40226777000048092, 44191311020023305, 34517118751878097,
    53021082385602761, 40189544093849117, 35254084346043827, 34517118751878097, 35254084346043827, 39198942791851366,
    39375099747005196, 46258536644010401, 14263342565830274, 13900772490874059, 11093417564387961, 14326078321178237,
    17887833434243992, 14056891688362847, 13900772490874059, 17887833434243992, 11093417564387961, 14056891688362847,
    14056891688362847, 14056891688362847, 14056891688362847, 14056891688362847, 14263342565830274, 14326078321178237,
    25591666862722697, 32910410245231846, 38229232651774404, 32910410245231846, 27591502237282789, 47568125048107767,
    15207433824679617, 53735298943909324, 19836480355810319, 14862298340817341, 56735298525419052, 13900772490874059,
    13900772490874059, 18981519917909408, 14782127990393705, 19836480355810319, 18981519917909408, 51568143208818718,
    14862298340817341, 14782127990393705, 15207433824679617, 20618974208723429, 27937717594428827, 33256539997770140,
    27937717594428827, 22618809583283499, 30712720269852486, 12400078902622020
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
noncomputable def negativeCeiling : ℝ := 103586843427 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 263297819403065852938835460096, coefficient := (-263297819403065852938835460096) }, { argument := 379111417269302656746941054976, coefficient := (-379111417269302656746941054976) }, { argument := 41161938381742197371452952412160, coefficient := (-41161938381742197371452952412160) }, { argument := 1445632902404745243339572379648, coefficient := (-1445632902404745243339572379648) }, { argument := 420258482539491941055192891392000, coefficient := (-420258482539491941055192891392000) }, { argument := 1483427226650620935975901069312, coefficient := (-1483427226650620935975901069312) }, { argument := 47242905307344615795410862080, coefficient := (-47242905307344615795410862080) }, { argument := 1445632902404745243339572379648, coefficient := (-1445632902404745243339572379648) }, { argument := 822026552347796314840149000192, coefficient := (-822026552347796314840149000192) }, { argument := 1483427226650620935975901069312, coefficient := (-1483427226650620935975901069312) }, { argument := 23158472181660330662910404591616, coefficient := (-23158472181660330662910404591616) }, { argument := 907063781901016623271888551936, coefficient := (-907063781901016623271888551936) }, { argument := 41161953259038123409968568729600, coefficient := (-41161953259038123409968568729600) }, { argument := 1445632902404745243339572379648, coefficient := (-1445632902404745243339572379648) }, { argument := 47242905307344615795410862080, coefficient := (-47242905307344615795410862080) }, { argument := 907063781901016623271888551936, coefficient := (-907063781901016623271888551936) }, { argument := 47242905307344615795410862080, coefficient := (-47242905307344615795410862080) }, { argument := 1455081483466214166498654552064, coefficient := (-1455081483466214166498654552064) }, { argument := 822026552347796314840149000192, coefficient := (-822026552347796314840149000192) }, { argument := 379111413879713433202810945536, coefficient := (-379111413879713433202810945536) }, { argument := 185730673771263146254663680, coefficient := (-185730673771263146254663680) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 165093932241122796670812160, coefficient := (-165093932241122796670812160) }, { argument := 193985370383319286088204288, coefficient := (-193985370383319286088204288) }, { argument := 2290678309845578803807518720, coefficient := (-2290678309845578803807518720) }, { argument := 5150930685923031256129339392, coefficient := (-5150930685923031256129339392) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 2290678309845578803807518720, coefficient := (-2290678309845578803807518720) }, { argument := 165093932241122796670812160, coefficient := (-165093932241122796670812160) }, { argument := 160966583935094726754041856, coefficient := (-160966583935094726754041856) }, { argument := 160966583935094726754041856, coefficient := (-160966583935094726754041856) }, { argument := 160966583935094726754041856, coefficient := (-160966583935094726754041856) }, { argument := 5150930685923031256129339392, coefficient := (-5150930685923031256129339392) }, { argument := 160966583935094726754041856, coefficient := (-160966583935094726754041856) }, { argument := 185730673771263146254663680, coefficient := (-185730673771263146254663680) }, { argument := 193985370383319286088204288, coefficient := (-193985370383319286088204288) }, { argument := 932779702591419747164749824, coefficient := (-932779702591419747164749824) }, { argument := 148915661264420328206990573568, coefficient := (-148915661264420328206990573568) }, { argument := 1485954359915783833652180287488, coefficient := (-1485954359915783833652180287488) }, { argument := 148915661264420328206990573568, coefficient := (-148915661264420328206990573568) }, { argument := 932673269489800461479313408, coefficient := (-932673269489800461479313408) }, { argument := 939706544569202978070892380160, coefficient := (-939706544569202978070892380160) }, { argument := 178670735879373026660188160, coefficient := (-178670735879373026660188160) }, { argument := 33764987004290648756126656495616, coefficient := (-33764987004290648756126656495616) }, { argument := 4421150336759804893740400640, coefficient := (-4421150336759804893740400640) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 33764977209901599439785306357760, coefficient := (-33764977209901599439785306357760) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 2444367727030571407287255040, coefficient := (-2444367727030571407287255040) }, { argument := 133052675654852253895884800, coefficient := (-133052675654852253895884800) }, { argument := 4421150336759804893740400640, coefficient := (-4421150336759804893740400640) }, { argument := 2444367727030571407287255040, coefficient := (-2444367727030571407287255040) }, { argument := 939718373712481754492405022720, coefficient := (-939718373712481754492405022720) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 133052675654852253895884800, coefficient := (-133052675654852253895884800) }, { argument := 178670735879373026660188160, coefficient := (-178670735879373026660188160) }, { argument := 29706359955140756279132160, coefficient := (-29706359955140756279132160) }, { argument := 4742536982943322554362757120, coefficient := (-4742536982943322554362757120) }, { argument := 47323387258464453301024849920, coefficient := (-47323387258464453301024849920) }, { argument := 4742536982943322554362757120, coefficient := (-4742536982943322554362757120) }, { argument := 29702970365917212149022720, coefficient := (-29702970365917212149022720) }, { argument := 8115397200163456853496299520, coefficient := (-8115397200163456853496299520) }, { argument := 204195126719283459040215040, coefficient := (-204195126719283459040215040) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
