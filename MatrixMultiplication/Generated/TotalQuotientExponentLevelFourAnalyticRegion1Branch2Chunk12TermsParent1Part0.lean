import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 12, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-320113738649274132333203344588800)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1, 13799631043, 13661260605, 13799631043, 13661260605, 115504622793,
    758635839, 628752013751, 333792549, 63590043, 1333158543, 663010383,
    115517205705, 758635839, 63540891, 1425, 28557, 47937,
    45999, 1425, 45999, 30723, 741, 28557,
    171, 85411045607, 3958514810649, 8380445, 78776183, 930229395,
    65367471, 1979257379435, 930229395, 8380445, 65367471, 65367471,
    65367471, 65367471, 65367471, 42705548693, 78776183, 1,
    50096025745, 49601014639, 50096025745, 49601014639, 4264379896631, 28052440513,
    23120394888777, 12177845083, 2344185701, 48635797361, 24425304241, 4264391299895,
    28052440513, 2344141157, 22425, 449397, 754377, 723879,
    22425, 723879, 483483, 11661
  ]
def negativeCoefficients : Array ℕ := #[
    39614081257132168796771975168, 31819782770229826080720551936, 31500722263085689212984360960, 31819782770229826080720551936, 31500722263085689212984360960, 4161492609360995991498522624,
    13994361167176923532517965824, 45306357357399241231419047936, 12314771450228310239103418368, 586514624428592778386079744, 12296217226200255218784927744, 12230382853413150047682428928,
    4161945956543351477439037440, 13994361167176923532517965824, 586061277246237292445564928, 13458744476178488859033600, 269713239302616916735033344, 452752164178644365217890304,
    434448271691041620369604608, 13458744476178488859033600, 434448271691041620369604608, 290170530906408219800764416, 13997094255225628413394944, 269713239302616916735033344,
    12920394697131349304672256, 384657153169009639342211072, 17827565826179425931209211904, 154591924138798843292549120, 181645510863088640868745216, 2144962947425833950684119040,
    4823268033130523910727532544, 17827565592987540825592299520, 2144962947425833950684119040, 154591924138798843292549120, 150727126035328872210235392, 150727126035328872210235392,
    150727126035328872210235392, 4823268033130523910727532544, 150727126035328872210235392, 384657386360894744959123456, 181645510863088640868745216, 39614081257132168796771975168,
    115513570753497484425942794240, 114372152855244245592417763328, 115513570753497484425942794240, 114372152855244245592417763328, 153640477707468846806553591808, 517476190786272483947743019008,
    1666000028892077080174261174272, 449283183230766505434080608256, 21621296843798210462674321408, 448586053369582699982973042688, 450567336256219527688493203456, 153640888553352856465687183360,
    517476190786272483947743019008, 21620885997914200803540729856, 105899068378351793917132800, 2122217330302169950099341312, 3562444660247754347372347392, 3418421927253195907645046784,
    105899068378351793917132800, 3418421927253195907645046784, 2283183914237264676853383168, 110135031113485865673818112
  ]
def negativeScales : Array ℕ := #[
    0, 33, 33, 33, 33, 36,
    29, 39, 28, 25, 30, 29,
    36, 29, 25, 10, 14, 15,
    15, 10, 15, 14, 9, 14,
    7, 36, 41, 22, 26, 29,
    25, 40, 29, 22, 25, 25,
    25, 25, 25, 35, 26, 0,
    35, 35, 35, 35, 41, 34,
    44, 33, 31, 35, 34, 41,
    34, 31, 14, 18, 19, 19,
    14, 19, 18, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 33683910643495253, 33669371564649698, 33683910643495253, 33669371564649698, 36749159637156208,
    29498832287238362, 39193700159313630, 28314376509962606, 25922297555082428, 30312201214007121, 29304456222778115,
    36749316793776136, 29498832287238362, 25921181990901517, 10476746203939589, 14801556808026795, 15548852004421171,
    15489314877442711, 10476746203939589, 15489314877442711, 14907031481868981, 9533329732306630, 14801556808026795,
    7417852514885912, 36313703604339870, 41848096389508623, 22998595445260584, 26231256178899205, 29793011289018899,
    25962069558846065, 40848096370637579, 29793011289018899, 22998595445260584, 25962069558846065, 25962069558846065,
    25962069558846065, 25962069558846065, 25962069558846065, 35313704478949042, 26231256178899205, 0,
    35543977103883911, 35529650581576838, 35543977103883911, 35529650581576838, 41955473117859264, 34707407237185616,
    44394231272343818, 33503539814210283, 31126439715256621, 35501299519176890, 34507657481354156, 41955476975726992,
    34707407237185616, 31126412301038351, 14452820364694038, 18777630968521050, 19524926165175017, 19465389038197124,
    14452820364694038, 19465389038197124, 18883105640887843, 13509403893060724
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
noncomputable def negativeCeiling : ℝ := 2377348307 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 39614081257132168796771975168, coefficient := (-39614081257132168796771975168) }, { argument := 31819782770229826080720551936, coefficient := (-31819782770229826080720551936) }, { argument := 31500722263085689212984360960, coefficient := (-31500722263085689212984360960) }, { argument := 31819782770229826080720551936, coefficient := (-31819782770229826080720551936) }, { argument := 31500722263085689212984360960, coefficient := (-31500722263085689212984360960) }, { argument := 4161492609360995991498522624, coefficient := (-4161492609360995991498522624) }, { argument := 13994361167176923532517965824, coefficient := (-13994361167176923532517965824) }, { argument := 45306357357399241231419047936, coefficient := (-45306357357399241231419047936) }, { argument := 12314771450228310239103418368, coefficient := (-12314771450228310239103418368) }, { argument := 586514624428592778386079744, coefficient := (-586514624428592778386079744) }, { argument := 12296217226200255218784927744, coefficient := (-12296217226200255218784927744) }, { argument := 12230382853413150047682428928, coefficient := (-12230382853413150047682428928) }, { argument := 4161945956543351477439037440, coefficient := (-4161945956543351477439037440) }, { argument := 13994361167176923532517965824, coefficient := (-13994361167176923532517965824) }, { argument := 586061277246237292445564928, coefficient := (-586061277246237292445564928) }, { argument := 13458744476178488859033600, coefficient := (-13458744476178488859033600) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 452752164178644365217890304, coefficient := (-452752164178644365217890304) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 13458744476178488859033600, coefficient := (-13458744476178488859033600) }, { argument := 434448271691041620369604608, coefficient := (-434448271691041620369604608) }, { argument := 290170530906408219800764416, coefficient := (-290170530906408219800764416) }, { argument := 13997094255225628413394944, coefficient := (-13997094255225628413394944) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 12920394697131349304672256, coefficient := (-12920394697131349304672256) }, { argument := 384657153169009639342211072, coefficient := (-384657153169009639342211072) }, { argument := 17827565826179425931209211904, coefficient := (-17827565826179425931209211904) }, { argument := 154591924138798843292549120, coefficient := (-154591924138798843292549120) }, { argument := 181645510863088640868745216, coefficient := (-181645510863088640868745216) }, { argument := 2144962947425833950684119040, coefficient := (-2144962947425833950684119040) }, { argument := 4823268033130523910727532544, coefficient := (-4823268033130523910727532544) }, { argument := 17827565592987540825592299520, coefficient := (-17827565592987540825592299520) }, { argument := 2144962947425833950684119040, coefficient := (-2144962947425833950684119040) }, { argument := 154591924138798843292549120, coefficient := (-154591924138798843292549120) }, { argument := 150727126035328872210235392, coefficient := (-150727126035328872210235392) }, { argument := 150727126035328872210235392, coefficient := (-150727126035328872210235392) }, { argument := 150727126035328872210235392, coefficient := (-150727126035328872210235392) }, { argument := 4823268033130523910727532544, coefficient := (-4823268033130523910727532544) }, { argument := 150727126035328872210235392, coefficient := (-150727126035328872210235392) }, { argument := 384657386360894744959123456, coefficient := (-384657386360894744959123456) }, { argument := 181645510863088640868745216, coefficient := (-181645510863088640868745216) }, { argument := 39614081257132168796771975168, coefficient := (-39614081257132168796771975168) }, { argument := 115513570753497484425942794240, coefficient := (-115513570753497484425942794240) }, { argument := 114372152855244245592417763328, coefficient := (-114372152855244245592417763328) }, { argument := 115513570753497484425942794240, coefficient := (-115513570753497484425942794240) }, { argument := 114372152855244245592417763328, coefficient := (-114372152855244245592417763328) }, { argument := 153640477707468846806553591808, coefficient := (-153640477707468846806553591808) }, { argument := 517476190786272483947743019008, coefficient := (-517476190786272483947743019008) }, { argument := 1666000028892077080174261174272, coefficient := (-1666000028892077080174261174272) }, { argument := 449283183230766505434080608256, coefficient := (-449283183230766505434080608256) }, { argument := 21621296843798210462674321408, coefficient := (-21621296843798210462674321408) }, { argument := 448586053369582699982973042688, coefficient := (-448586053369582699982973042688) }, { argument := 450567336256219527688493203456, coefficient := (-450567336256219527688493203456) }, { argument := 153640888553352856465687183360, coefficient := (-153640888553352856465687183360) }, { argument := 517476190786272483947743019008, coefficient := (-517476190786272483947743019008) }, { argument := 21620885997914200803540729856, coefficient := (-21620885997914200803540729856) }, { argument := 105899068378351793917132800, coefficient := (-105899068378351793917132800) }, { argument := 2122217330302169950099341312, coefficient := (-2122217330302169950099341312) }, { argument := 3562444660247754347372347392, coefficient := (-3562444660247754347372347392) }, { argument := 3418421927253195907645046784, coefficient := (-3418421927253195907645046784) }, { argument := 105899068378351793917132800, coefficient := (-105899068378351793917132800) }, { argument := 3418421927253195907645046784, coefficient := (-3418421927253195907645046784) }, { argument := 2283183914237264676853383168, coefficient := (-2283183914237264676853383168) }, { argument := 110135031113485865673818112, coefficient := (-110135031113485865673818112) }] }

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


end Parent1

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-680308066998618605853066299179008)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    449397, 2691, 10639714286739, 419407724528493, 618873935, 5817414989,
    68695006785, 4827216693, 209703819733735, 68695006785, 618873935, 4827216693,
    4827216693, 4827216693, 4827216693, 4827216693, 5319899673881, 5817414989,
    675, 13527, 22707, 21789, 675, 21789,
    14553, 351, 13527, 81, 315330925, 26402385555,
    13201197555, 157660685, 5353207971, 666405466767, 1270333155, 26485518626253,
    41879115, 97717935, 1270333155, 1270333155, 41879115, 15676748715,
    628186725, 666405466767, 1270333155, 97717935, 628186725, 97717935,
    1270333155, 1270333155, 22305415023, 3449907627, 3415315029, 3449907627,
    3415315029, 34114669065601, 56100639383, 184959875544191, 24353849453, 4688016979,
    97264243303, 48846915623, 34114760291713, 56100639383
  ]
def negativeCoefficients : Array ℕ := #[
    2122217330302169950099341312, 101663105643217722160447488, 47917013297086303030732652544, 1888844471902828709979019542528, 22832418185669120511359057920, 26828091368161216600846893056,
    316799802326159047095106928640, 712371447392876559954402607104, 1888844088822037223425829765120, 316799802326159047095106928640, 22832418185669120511359057920, 22261607731027392498575081472,
    22261607731027392498575081472, 22261607731027392498575081472, 712371447392876559954402607104, 22261607731027392498575081472, 47917396377877789583922429952, 26828091368161216600846893056,
    12750389503748042076979200, 255517805655110763222663168, 428923102906084135469580288, 411582573180986798244888576, 12750389503748042076979200, 411582573180986798244888576,
    274898397700807787179671552, 13260405083897963760058368, 255517805655110763222663168, 12240373923598120393900032, 2908414436000550546204262400, 243519024634245460425902653440,
    243519112763565272573285498880, 2908326306680738398821416960, 385739286774917903318777856, 48019574588952362491588902912, 2929188824829125907248578560, 477120687263629367666332925952,
    1545066632876901577449799680, 112661108647274073355714560, 2929188824829125907248578560, 2929188824829125907248578560, 1545066632876901577449799680, 36148121431682509822419271680,
    2896999936644190457718374400, 48019574588952362491588902912, 2929188824829125907248578560, 112661108647274073355714560, 2896999936644190457718374400, 112661108647274073355714560,
    2929188824829125907248578560, 2929188824829125907248578560, 401818635143708253861445632, 31819781536603816151394287616, 31500721135528457707488018432, 31819781536603816151394287616,
    31500721135528457707488018432, 153638810891708450560955908096, 517437068534835963145920446464, 1665970453158623807332755177472, 449249228069142355304196866048, 21619662356204501372571222016,
    448552150933364798533415206912, 450533275643782880197957648384, 153639221737592460220089499648, 517437068534835963145920446464
  ]
def negativeScales : Array ℕ := #[
    18, 11, 43, 48, 29, 32,
    35, 32, 47, 35, 29, 32,
    32, 32, 32, 32, 42, 32,
    9, 13, 14, 14, 9, 14,
    13, 8, 13, 6, 28, 34,
    33, 27, 32, 39, 30, 44,
    25, 26, 30, 30, 25, 33,
    29, 39, 30, 26, 29, 26,
    30, 30, 34, 31, 31, 31,
    31, 44, 35, 47, 34, 32,
    36, 35, 44, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    18777630968521050, 11393926675640423, 43274524643525267, 48575346761239328, 29205070320601560, 32437731077391864,
    35999486210434834, 32168544444576446, 47575346468643075, 35999486210434834, 29205070320601560, 32168544444576446,
    32168544444576446, 32168544444576446, 32168544444576446, 32168544444576446, 42274536177352418, 32437731077391864,
    9398743691938200, 13723554295483443, 14470849492418713, 14411312365441260, 9398743691938200, 14411312365441260,
    13829028966070369, 8455327220304618, 13723554295483443, 6339850002884626, 28232291423431341, 34619949237288353,
    33619949759398319, 27232247706945328, 32317756556125822, 39277609279466384, 30242559758885168, 44590268992588670,
    25319727619407628, 26542120040745121, 30242559758885168, 30242559758885168, 25319727619407628, 33867907333515600,
    29226618215016146, 39277609279466384, 30242559758885168, 26542120040745121, 29226618215016146, 26542120040745121,
    30242559758885168, 30242559758885168, 34376674940565191, 31683910587563188, 31669371513008937, 31683910587563188,
    31669371513008937, 44955457466252521, 35707298162385835, 47394205660613934, 34503430776533521, 32126330648890352,
    36501190481625273, 35507548416781283, 44955461324162102, 35707298162385835
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
noncomputable def negativeCeiling : ℝ := 1464093003 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2122217330302169950099341312, coefficient := (-2122217330302169950099341312) }, { argument := 101663105643217722160447488, coefficient := (-101663105643217722160447488) }, { argument := 47917013297086303030732652544, coefficient := (-47917013297086303030732652544) }, { argument := 1888844471902828709979019542528, coefficient := (-1888844471902828709979019542528) }, { argument := 22832418185669120511359057920, coefficient := (-22832418185669120511359057920) }, { argument := 26828091368161216600846893056, coefficient := (-26828091368161216600846893056) }, { argument := 316799802326159047095106928640, coefficient := (-316799802326159047095106928640) }, { argument := 712371447392876559954402607104, coefficient := (-712371447392876559954402607104) }, { argument := 1888844088822037223425829765120, coefficient := (-1888844088822037223425829765120) }, { argument := 316799802326159047095106928640, coefficient := (-316799802326159047095106928640) }, { argument := 22832418185669120511359057920, coefficient := (-22832418185669120511359057920) }, { argument := 22261607731027392498575081472, coefficient := (-22261607731027392498575081472) }, { argument := 22261607731027392498575081472, coefficient := (-22261607731027392498575081472) }, { argument := 22261607731027392498575081472, coefficient := (-22261607731027392498575081472) }, { argument := 712371447392876559954402607104, coefficient := (-712371447392876559954402607104) }, { argument := 22261607731027392498575081472, coefficient := (-22261607731027392498575081472) }, { argument := 47917396377877789583922429952, coefficient := (-47917396377877789583922429952) }, { argument := 26828091368161216600846893056, coefficient := (-26828091368161216600846893056) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 428923102906084135469580288, coefficient := (-428923102906084135469580288) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 274898397700807787179671552, coefficient := (-274898397700807787179671552) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 12240373923598120393900032, coefficient := (-12240373923598120393900032) }, { argument := 2908414436000550546204262400, coefficient := (-2908414436000550546204262400) }, { argument := 243519024634245460425902653440, coefficient := (-243519024634245460425902653440) }, { argument := 243519112763565272573285498880, coefficient := (-243519112763565272573285498880) }, { argument := 2908326306680738398821416960, coefficient := (-2908326306680738398821416960) }, { argument := 385739286774917903318777856, coefficient := (-385739286774917903318777856) }, { argument := 48019574588952362491588902912, coefficient := (-48019574588952362491588902912) }, { argument := 2929188824829125907248578560, coefficient := (-2929188824829125907248578560) }, { argument := 477120687263629367666332925952, coefficient := (-477120687263629367666332925952) }, { argument := 1545066632876901577449799680, coefficient := (-1545066632876901577449799680) }, { argument := 112661108647274073355714560, coefficient := (-112661108647274073355714560) }, { argument := 2929188824829125907248578560, coefficient := (-2929188824829125907248578560) }, { argument := 2929188824829125907248578560, coefficient := (-2929188824829125907248578560) }, { argument := 1545066632876901577449799680, coefficient := (-1545066632876901577449799680) }, { argument := 36148121431682509822419271680, coefficient := (-36148121431682509822419271680) }, { argument := 2896999936644190457718374400, coefficient := (-2896999936644190457718374400) }, { argument := 48019574588952362491588902912, coefficient := (-48019574588952362491588902912) }, { argument := 2929188824829125907248578560, coefficient := (-2929188824829125907248578560) }, { argument := 112661108647274073355714560, coefficient := (-112661108647274073355714560) }, { argument := 2896999936644190457718374400, coefficient := (-2896999936644190457718374400) }, { argument := 112661108647274073355714560, coefficient := (-112661108647274073355714560) }, { argument := 2929188824829125907248578560, coefficient := (-2929188824829125907248578560) }, { argument := 2929188824829125907248578560, coefficient := (-2929188824829125907248578560) }, { argument := 401818635143708253861445632, coefficient := (-401818635143708253861445632) }, { argument := 31819781536603816151394287616, coefficient := (-31819781536603816151394287616) }, { argument := 31500721135528457707488018432, coefficient := (-31500721135528457707488018432) }, { argument := 31819781536603816151394287616, coefficient := (-31819781536603816151394287616) }, { argument := 31500721135528457707488018432, coefficient := (-31500721135528457707488018432) }, { argument := 153638810891708450560955908096, coefficient := (-153638810891708450560955908096) }, { argument := 517437068534835963145920446464, coefficient := (-517437068534835963145920446464) }, { argument := 1665970453158623807332755177472, coefficient := (-1665970453158623807332755177472) }, { argument := 449249228069142355304196866048, coefficient := (-449249228069142355304196866048) }, { argument := 21619662356204501372571222016, coefficient := (-21619662356204501372571222016) }, { argument := 448552150933364798533415206912, coefficient := (-448552150933364798533415206912) }, { argument := 450533275643782880197957648384, coefficient := (-450533275643782880197957648384) }, { argument := 153639221737592460220089499648, coefficient := (-153639221737592460220089499648) }, { argument := 517437068534835963145920446464, coefficient := (-517437068534835963145920446464) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
