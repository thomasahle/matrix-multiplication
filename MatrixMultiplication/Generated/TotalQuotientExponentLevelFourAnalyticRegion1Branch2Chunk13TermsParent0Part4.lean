import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 13, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13

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
def constantNumerator : ℤ := (-240253266839953880542887035357102080)
def positiveArguments : Array ℕ := #[
    459, 15249, 39321, 51, 459, 459,
    969, 29, 4431282741, 4431281611, 96701100243, 337596686449,
    24175274927, 15712447933, 2397, 288765442299, 59313, 1887,
    288755856777, 969, 969, 32793, 1785, 59313,
    32793, 15731627323, 1887, 1785, 2397, 323390721,
    41983793009, 22185, 218904502227, 22765, 725, 22185,
    12615, 22765, 355395, 435, 20991901479, 22185,
    725, 435, 725, 11165, 12615, 161693389,
    102315731, 7851192621, 4305, 3813, 178473, 48585,
    3925596777, 178473, 4305, 4305
  ]
def positiveCoefficients : Array ℕ := #[
    35513404876999346636168626176, 294958557172855684561511645184, 1521157508898138680915889487872, 31567471001777197009927667712, 35513404876999346636168626176, 35513404876999346636168626176,
    37486371814610421449289105408, 2297616712913665790212774559744, 83704564368868523952977366482944, 83704543023772021382181000577024, 456658034644160904111462052528128, 1594255276814610544948002112405504,
    456658032117694835776201863200768, 74199937482633636846381058490368, 46364723033860258108331261952, 2727312492247652213788267625054208, 1147280274220840003829558673408, 36499888345804884042728865792,
    2727221959552024994573611469635584, 37486371814610421449289105408, 37486371814610421449289105408, 634308870441960552418234073088, 34526921408193809229608386560, 1147280274220840003829558673408,
    634308870441960552418234073088, 74290509591131522091096167415808, 36499888345804884042728865792, 34526921408193809229608386560, 46364723033860258108331261952, 1527169501721448714671348514816,
    198262856929438528981080435851264, 858240617860817543707408465920, 2067494568532096816064431845801984, 880678281072865061189955092480, 28047079015059396853183283200, 858240617860817543707408465920,
    488019174862033505245389127680, 880678281072865061189955092480, 13748678133182116337430445424640, 538503917089140419581119037440, 198262903912262667051180666912768, 858240617860817543707408465920,
    28047079015059396853183283200, 538503917089140419581119037440, 28047079015059396853183283200, 863850033663829423078045122560, 488019174862033505245389127680, 1527150881430406759660270911488,
    966344757489413455499914903552, 74152417767927762813316006674432, 83270810455055657553761402880, 73754146403049296690474385408, 3452169884865307403157365587968, 939770575135628135249592975360,
    74152426579863619848073975431168, 3452169884865307403157365587968, 83270810455055657553761402880, 83270810455055657553761402880
  ]
def positiveScales : Array ℕ := #[
    8, 13, 15, 5, 8, 8,
    9, 4, 32, 32, 36, 38,
    34, 33, 11, 38, 15, 10,
    38, 9, 9, 15, 10, 15,
    15, 33, 10, 10, 11, 28,
    35, 14, 37, 14, 9, 14,
    13, 14, 18, 8, 34, 14,
    9, 8, 9, 13, 13, 27,
    26, 32, 12, 11, 17, 15,
    31, 17, 12, 12
  ]
def negativeArguments : Array ℕ := #[
    51, 29, 2113, 15825, 70769, 31405
  ]
def negativeCoefficients : Array ℕ := #[
    4040636288227481217270741467136, 2297616712913665790212774559744, 167409107392640545335158367059968, 2507571343576466284835666028134400, 5606897832971972907157511821328384, 2488160443760471522125247760302080
  ]
def negativeScales : Array ℕ := #[
    5, 4, 11, 13, 16, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8842350343321225, 13896427015916396, 15263012391886529, 5672425341969176, 8842350343321225, 8842350343321225,
    9920352855028171, 4857980995002857, 32045077235882297, 32045076867987559, 36492813253323293, 38296509787654852,
    34492813245341566, 33871188912648370, 11227014193649132, 38071107143302607, 15856060723324442, 10881878707405986,
    38071059252479958, 9920352855028171, 9920352855028171, 15001100269299442, 10801708358875019, 15856060723324442,
    15001100269299442, 33872948863542980, 10881878707405986, 10801708358875019, 11227014193649132, 28268703043478392,
    35289113461098665, 14437296932707584, 37671510670610927, 14474529838906553, 9501837184902278, 14437296932707584,
    13622852585863008, 14474529838906553, 18439063858881771, 8764871590716857, 34289113802977524, 14437296932707584,
    9501837184902278, 8764871590716857, 9501837184902278, 13446695630709832, 13622852585863008, 27268685453050293,
    26608452734982505, 32870264674421373, 12071797522284206, 11896710815471615, 17445346309405981, 15568223348403562,
    31870264845864675, 17445346309405981, 12071797522284206, 12071797522284206
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    5672425342008812, 4857980997143165, 11045077051934941, 13949917889612672, 16110829913017350, 14938706657490799
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
noncomputable def positiveFloor : ℝ := 2459807064859 / 500000000000
noncomputable def negativeCeiling : ℝ := 1978474358417 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 35513404876999346636168626176, coefficient := 35513404876999346636168626176 }, { argument := 294958557172855684561511645184, coefficient := 294958557172855684561511645184 }, { argument := 1521157508898138680915889487872, coefficient := 1521157508898138680915889487872 }, { argument := 31567471001777197009927667712, coefficient := 31567471001777197009927667712 }, { argument := 35513404876999346636168626176, coefficient := 35513404876999346636168626176 }, { argument := 35513404876999346636168626176, coefficient := 35513404876999346636168626176 }, { argument := 37486371814610421449289105408, coefficient := 37486371814610421449289105408 }, { argument := 4040636288227481217270741467136, coefficient := (-4040636288227481217270741467136) }, { argument := 2297616712913665790212774559744, coefficient := 2297616712913665790212774559744 }, { argument := 2297616712913665790212774559744, coefficient := (-2297616712913665790212774559744) }, { argument := 83704564368868523952977366482944, coefficient := 83704564368868523952977366482944 }, { argument := 83704543023772021382181000577024, coefficient := 83704543023772021382181000577024 }, { argument := 167409107392640545335158367059968, coefficient := (-167409107392640545335158367059968) }, { argument := 456658034644160904111462052528128, coefficient := 456658034644160904111462052528128 }, { argument := 1594255276814610544948002112405504, coefficient := 1594255276814610544948002112405504 }, { argument := 456658032117694835776201863200768, coefficient := 456658032117694835776201863200768 }, { argument := 2507571343576466284835666028134400, coefficient := (-2507571343576466284835666028134400) }, { argument := 74199937482633636846381058490368, coefficient := 74199937482633636846381058490368 }, { argument := 46364723033860258108331261952, coefficient := 46364723033860258108331261952 }, { argument := 2727312492247652213788267625054208, coefficient := 2727312492247652213788267625054208 }, { argument := 1147280274220840003829558673408, coefficient := 1147280274220840003829558673408 }, { argument := 36499888345804884042728865792, coefficient := 36499888345804884042728865792 }, { argument := 2727221959552024994573611469635584, coefficient := 2727221959552024994573611469635584 }, { argument := 37486371814610421449289105408, coefficient := 37486371814610421449289105408 }, { argument := 37486371814610421449289105408, coefficient := 37486371814610421449289105408 }, { argument := 634308870441960552418234073088, coefficient := 634308870441960552418234073088 }, { argument := 34526921408193809229608386560, coefficient := 34526921408193809229608386560 }, { argument := 1147280274220840003829558673408, coefficient := 1147280274220840003829558673408 }, { argument := 634308870441960552418234073088, coefficient := 634308870441960552418234073088 }, { argument := 74290509591131522091096167415808, coefficient := 74290509591131522091096167415808 }, { argument := 36499888345804884042728865792, coefficient := 36499888345804884042728865792 }, { argument := 34526921408193809229608386560, coefficient := 34526921408193809229608386560 }, { argument := 46364723033860258108331261952, coefficient := 46364723033860258108331261952 }, { argument := 5606897832971972907157511821328384, coefficient := (-5606897832971972907157511821328384) }, { argument := 1527169501721448714671348514816, coefficient := 1527169501721448714671348514816 }, { argument := 198262856929438528981080435851264, coefficient := 198262856929438528981080435851264 }, { argument := 858240617860817543707408465920, coefficient := 858240617860817543707408465920 }, { argument := 2067494568532096816064431845801984, coefficient := 2067494568532096816064431845801984 }, { argument := 880678281072865061189955092480, coefficient := 880678281072865061189955092480 }, { argument := 28047079015059396853183283200, coefficient := 28047079015059396853183283200 }, { argument := 858240617860817543707408465920, coefficient := 858240617860817543707408465920 }, { argument := 488019174862033505245389127680, coefficient := 488019174862033505245389127680 }, { argument := 880678281072865061189955092480, coefficient := 880678281072865061189955092480 }, { argument := 13748678133182116337430445424640, coefficient := 13748678133182116337430445424640 }, { argument := 538503917089140419581119037440, coefficient := 538503917089140419581119037440 }, { argument := 198262903912262667051180666912768, coefficient := 198262903912262667051180666912768 }, { argument := 858240617860817543707408465920, coefficient := 858240617860817543707408465920 }, { argument := 28047079015059396853183283200, coefficient := 28047079015059396853183283200 }, { argument := 538503917089140419581119037440, coefficient := 538503917089140419581119037440 }, { argument := 28047079015059396853183283200, coefficient := 28047079015059396853183283200 }, { argument := 863850033663829423078045122560, coefficient := 863850033663829423078045122560 }, { argument := 488019174862033505245389127680, coefficient := 488019174862033505245389127680 }, { argument := 1527150881430406759660270911488, coefficient := 1527150881430406759660270911488 }, { argument := 2488160443760471522125247760302080, coefficient := (-2488160443760471522125247760302080) }, { argument := 966344757489413455499914903552, coefficient := 966344757489413455499914903552 }, { argument := 74152417767927762813316006674432, coefficient := 74152417767927762813316006674432 }, { argument := 83270810455055657553761402880, coefficient := 83270810455055657553761402880 }, { argument := 73754146403049296690474385408, coefficient := 73754146403049296690474385408 }, { argument := 3452169884865307403157365587968, coefficient := 3452169884865307403157365587968 }, { argument := 939770575135628135249592975360, coefficient := 939770575135628135249592975360 }, { argument := 74152426579863619848073975431168, coefficient := 74152426579863619848073975431168 }, { argument := 3452169884865307403157365587968, coefficient := 3452169884865307403157365587968 }, { argument := 83270810455055657553761402880, coefficient := 83270810455055657553761402880 }, { argument := 83270810455055657553761402880, coefficient := 83270810455055657553761402880 }] }

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
def constantNumerator : ℤ := (-15193810546602278537176176853516288)
def positiveArguments : Array ℕ := #[
    1845, 4305, 48585, 1845, 51157399, 3813,
    13228131, 1503, 67743645, 2421, 75, 2421,
    1617, 13240419, 1503, 9
  ]
def positiveCoefficients : Array ℕ := #[
    71374980390047706474652631040, 83270810455055657553761402880, 939770575135628135249592975360, 71374980390047706474652631040, 966335945553556420741946146816, 73754146403049296690474385408,
    124936164930817845620587364352, 58144496220185204786668240896, 1279641274301679306530283847680, 93657901097184551422836867072, 2901421967075110019294822400, 93657901097184551422836867072,
    62554657610139372015996370944, 125052221809500850021359157248, 58144496220185204786668240896, 2785365088392105618523029504
  ]
def positiveScales : Array ℕ := #[
    10, 12, 15, 10, 25, 11,
    23, 10, 26, 11, 6, 11,
    10, 23, 10, 3
  ]
def negativeArguments : Array ℕ := #[
    2015, 3
  ]
def negativeCoefficients : Array ℕ := #[
    159644747466242640250991059927040, 1901475900342344102245054808064
  ]
def negativeScales : Array ℕ := #[
    10, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10849405100841772, 12071797522284206, 15568223348403562, 10849405100841772, 25608439579228281, 11896710815471615,
    23657105902129704, 10553629293916271, 26013582278471260, 11241387363998936, 6228818690495880, 11241387363998936,
    10659103963471994, 23658445441918271, 10553629293916271, 3169925001442312
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    10976564139628376, 1584962500724866
  ]

abbrev PositiveTerm := Fin 16
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 1035634977 / 1000000000000
noncomputable def negativeCeiling : ℝ := 21129432527 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 71374980390047706474652631040, coefficient := 71374980390047706474652631040 }, { argument := 83270810455055657553761402880, coefficient := 83270810455055657553761402880 }, { argument := 939770575135628135249592975360, coefficient := 939770575135628135249592975360 }, { argument := 71374980390047706474652631040, coefficient := 71374980390047706474652631040 }, { argument := 966335945553556420741946146816, coefficient := 966335945553556420741946146816 }, { argument := 73754146403049296690474385408, coefficient := 73754146403049296690474385408 }, { argument := 159644747466242640250991059927040, coefficient := (-159644747466242640250991059927040) }, { argument := 124936164930817845620587364352, coefficient := 124936164930817845620587364352 }, { argument := 58144496220185204786668240896, coefficient := 58144496220185204786668240896 }, { argument := 1279641274301679306530283847680, coefficient := 1279641274301679306530283847680 }, { argument := 93657901097184551422836867072, coefficient := 93657901097184551422836867072 }, { argument := 2901421967075110019294822400, coefficient := 2901421967075110019294822400 }, { argument := 93657901097184551422836867072, coefficient := 93657901097184551422836867072 }, { argument := 62554657610139372015996370944, coefficient := 62554657610139372015996370944 }, { argument := 125052221809500850021359157248, coefficient := 125052221809500850021359157248 }, { argument := 58144496220185204786668240896, coefficient := 58144496220185204786668240896 }, { argument := 2785365088392105618523029504, coefficient := 2785365088392105618523029504 }, { argument := 1901475900342344102245054808064, coefficient := (-1901475900342344102245054808064) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13
