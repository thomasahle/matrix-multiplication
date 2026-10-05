import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 2,
parent chunk 4, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk4

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
def constantNumerator : ℤ := 18453400153938498172157251551232
def positiveArguments : Array ℕ := #[
    3, 223251, 2041445, 8165787, 111199, 42211
  ]
def positiveCoefficients : Array ℕ := #[
    475368975085586025561263702016, 2108546079334262327205691392, 77123611556974582986189045760, 77123677670105343161222037504, 2100489722114486712471126016, 1594686492867284752922574848
  ]
def positiveScales : Array ℕ := #[
    1, 17, 20, 22, 16, 15
  ]
def negativeArguments : Array ℕ := #[
    18256797027, 918209261151, 1835677105731, 36921027129, 1778338617, 47583638607,
    1219139350229, 94987165805, 1757829335, 166943247765, 8396261181945, 16785742725045,
    337612132655, 47583638607, 39775501215, 16325984935399, 635181870389, 367386175,
    18256797027, 166943247765, 667773563499, 9093520623, 667773563499, 33585073518087,
    67143028457547, 1350449688273, 1219139350229, 16325984935399, 52084479131735, 32593570814759,
    602908892095, 918209261151, 8396261181945, 33585073518087, 457350478299, 9093520623,
    457350478299, 914331664719, 18389979421, 94987165805, 635181870389, 32593570814759,
    633955707009, 23467699045, 1835677105731, 16785742725045, 67143028457547, 914331664719,
    1757829335, 367386175, 602908892095, 23467699045, 54291625, 36921027129,
    337612132655, 1350449688273, 18389979421, 1
  ]
def negativeCoefficients : Array ℕ := #[
    10277663035971997400039424, 516905860795972756137050112, 516697170583917636706369536, 10392345251268773359386624, 2002231283214940800811008, 53574414274854386839584768,
    686314440425504127160680448, 53473020565547189964636160, 1979139884521731695575040, 375922774213237194589470720, 18906699365156431158690447360, 18899066170412419023718318080,
    380117468705204116096286720, 53574414274854386839584768, 1433063459602789687225221120, 18381424917879816902699646976, 1430302417398197543577321472, 52945927706594298665369600,
    10277663035971997400039424, 375922774213237194589470720, 375923096467745581131890688, 10238394022307180159434752, 375923096467745581131890688, 18906715572658415793963270144,
    18899082371370954875398520832, 380117794555555330117337088, 686314440425504127160680448, 18381424917879816902699646976, 234567640809468121043236290560, 18348549172002813263434743808,
    678815065444350145362657280, 516905860795972756137050112, 18906699365156431158690447360, 18906715572658415793963270144, 514930860911273629320216576, 10238394022307180159434752,
    514930860911273629320216576, 514722968065191710533091328, 10352638058470836222820352, 53473020565547189964636160, 1430302417398197543577321472, 18348549172002813263434743808,
    1427541342927565869633503232, 52844560337152472420188160, 516697170583917636706369536, 18899066170412419023718318080, 18899082371370954875398520832, 514722968065191710533091328,
    1979139884521731695575040, 52945927706594298665369600, 678815065444350145362657280, 52844560337152472420188160, 1956061936954709639168000, 10392345251268773359386624,
    380117468705204116096286720, 380117794555555330117337088, 10352638058470836222820352, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    34, 39, 40, 35, 30, 35,
    40, 36, 30, 37, 42, 43,
    38, 35, 35, 43, 39, 28,
    34, 37, 39, 33, 39, 44,
    45, 40, 40, 43, 45, 44,
    39, 39, 42, 44, 38, 33,
    38, 39, 34, 36, 39, 44,
    39, 34, 40, 43, 45, 39,
    30, 28, 39, 34, 25, 35,
    38, 40, 34, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    1584962500720924, 17768307111987966, 20961159267977216, 22961160504706693, 16762784288545236, 15365331387427179
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    34087714629935842, 39740032027232575, 40739449450885249, 35103723637645568, 30727882910886365, 35469746544293030,
    40149000177153023, 36467013545682480, 30711147862274086, 37280566786680141, 42932884191581048, 43932301615158260,
    38296575794389867, 35469746544293030, 35211161059086489, 43892235268526182, 39208378778859695, 28452722096941211,
    34087714629935842, 37280566786680141, 39280568023409634, 33082191806490810, 39280568023409634, 44932885428310706,
    45932302851887917, 40296577031119360, 40149000177153023, 43892235268526182, 45565918755452976, 44889652653505425,
    39133149051104417, 39740032027232575, 42932884191581048, 44932885428310706, 38734509203766654, 33082191806490810,
    38734509203766654, 39733926627419579, 34098200814200535, 36467013545682480, 39208378778859695, 44889652653505425,
    39205591089944714, 34449957344671653, 40739449450885249, 43932301615158260, 45932302851887917, 39733926627419579,
    30711147862274086, 28452722096941211, 39133149051104417, 34449957344671653, 25694226330023569, 35103723637645568,
    38296575794389867, 40296577031119360, 34098200814200535, 0
  ]

abbrev PositiveTerm := Fin 6
abbrev NegativeTerm := Fin 58
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
noncomputable def positiveFloor : ℝ := 12753477 / 250000000000
noncomputable def negativeCeiling : ℝ := 256316613 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 10277663035971997400039424, coefficient := (-10277663035971997400039424) }, { argument := 516905860795972756137050112, coefficient := (-516905860795972756137050112) }, { argument := 516697170583917636706369536, coefficient := (-516697170583917636706369536) }, { argument := 10392345251268773359386624, coefficient := (-10392345251268773359386624) }, { argument := 2002231283214940800811008, coefficient := (-2002231283214940800811008) }, { argument := 53574414274854386839584768, coefficient := (-53574414274854386839584768) }, { argument := 686314440425504127160680448, coefficient := (-686314440425504127160680448) }, { argument := 53473020565547189964636160, coefficient := (-53473020565547189964636160) }, { argument := 1979139884521731695575040, coefficient := (-1979139884521731695575040) }, { argument := 375922774213237194589470720, coefficient := (-375922774213237194589470720) }, { argument := 18906699365156431158690447360, coefficient := (-18906699365156431158690447360) }, { argument := 18899066170412419023718318080, coefficient := (-18899066170412419023718318080) }, { argument := 380117468705204116096286720, coefficient := (-380117468705204116096286720) }, { argument := 53574414274854386839584768, coefficient := (-53574414274854386839584768) }, { argument := 1433063459602789687225221120, coefficient := (-1433063459602789687225221120) }, { argument := 18381424917879816902699646976, coefficient := (-18381424917879816902699646976) }, { argument := 1430302417398197543577321472, coefficient := (-1430302417398197543577321472) }, { argument := 52945927706594298665369600, coefficient := (-52945927706594298665369600) }, { argument := 10277663035971997400039424, coefficient := (-10277663035971997400039424) }, { argument := 375922774213237194589470720, coefficient := (-375922774213237194589470720) }, { argument := 375923096467745581131890688, coefficient := (-375923096467745581131890688) }, { argument := 10238394022307180159434752, coefficient := (-10238394022307180159434752) }, { argument := 375923096467745581131890688, coefficient := (-375923096467745581131890688) }, { argument := 18906715572658415793963270144, coefficient := (-18906715572658415793963270144) }, { argument := 18899082371370954875398520832, coefficient := (-18899082371370954875398520832) }, { argument := 380117794555555330117337088, coefficient := (-380117794555555330117337088) }, { argument := 686314440425504127160680448, coefficient := (-686314440425504127160680448) }, { argument := 18381424917879816902699646976, coefficient := (-18381424917879816902699646976) }, { argument := 234567640809468121043236290560, coefficient := (-234567640809468121043236290560) }, { argument := 18348549172002813263434743808, coefficient := (-18348549172002813263434743808) }, { argument := 678815065444350145362657280, coefficient := (-678815065444350145362657280) }, { argument := 516905860795972756137050112, coefficient := (-516905860795972756137050112) }, { argument := 18906699365156431158690447360, coefficient := (-18906699365156431158690447360) }, { argument := 18906715572658415793963270144, coefficient := (-18906715572658415793963270144) }, { argument := 514930860911273629320216576, coefficient := (-514930860911273629320216576) }, { argument := 10238394022307180159434752, coefficient := (-10238394022307180159434752) }, { argument := 514930860911273629320216576, coefficient := (-514930860911273629320216576) }, { argument := 514722968065191710533091328, coefficient := (-514722968065191710533091328) }, { argument := 10352638058470836222820352, coefficient := (-10352638058470836222820352) }, { argument := 53473020565547189964636160, coefficient := (-53473020565547189964636160) }, { argument := 1430302417398197543577321472, coefficient := (-1430302417398197543577321472) }, { argument := 18348549172002813263434743808, coefficient := (-18348549172002813263434743808) }, { argument := 1427541342927565869633503232, coefficient := (-1427541342927565869633503232) }, { argument := 52844560337152472420188160, coefficient := (-52844560337152472420188160) }, { argument := 516697170583917636706369536, coefficient := (-516697170583917636706369536) }, { argument := 18899066170412419023718318080, coefficient := (-18899066170412419023718318080) }, { argument := 18899082371370954875398520832, coefficient := (-18899082371370954875398520832) }, { argument := 514722968065191710533091328, coefficient := (-514722968065191710533091328) }, { argument := 1979139884521731695575040, coefficient := (-1979139884521731695575040) }, { argument := 52945927706594298665369600, coefficient := (-52945927706594298665369600) }, { argument := 678815065444350145362657280, coefficient := (-678815065444350145362657280) }, { argument := 52844560337152472420188160, coefficient := (-52844560337152472420188160) }, { argument := 1956061936954709639168000, coefficient := (-1956061936954709639168000) }, { argument := 10392345251268773359386624, coefficient := (-10392345251268773359386624) }, { argument := 380117468705204116096286720, coefficient := (-380117468705204116096286720) }, { argument := 380117794555555330117337088, coefficient := (-380117794555555330117337088) }, { argument := 10352638058470836222820352, coefficient := (-10352638058470836222820352) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 2108546079334262327205691392, coefficient := 2108546079334262327205691392 }, { argument := 77123611556974582986189045760, coefficient := 77123611556974582986189045760 }, { argument := 77123677670105343161222037504, coefficient := 77123677670105343161222037504 }, { argument := 2100489722114486712471126016, coefficient := 2100489722114486712471126016 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 1594686492867284752922574848, coefficient := 1594686492867284752922574848 }] }

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
def constantNumerator : ℤ := (-19643076173050868431978806378496)
def positiveArguments : Array ℕ := #[
    1130329, 28869291, 2256571, 41745, 81777, 4112901,
    8222481, 165379
  ]
def positiveCoefficients : Array ℕ := #[
    42702622273724505638014287872, 545325488810441210963788038144, 42625421026462552678060785664, 1577081510619146715565916160, 1544723855478523906561671168, 77690503319044186676221968384,
    77659137360864966492712599552, 1561960493140998111591661568
  ]
def positiveScales : Array ℕ := #[
    20, 24, 21, 15, 16, 21,
    22, 17
  ]
def negativeArguments : Array ℕ := #[
    1, 1
  ]
def negativeCoefficients : Array ℕ := #[
    633825300114114700748351602688, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    0, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    20108311322128413, 24783032341090630, 21105700741066000, 15349315788940125, 16319407517927179, 21971724914119468,
    22971142337783268, 17335416525636905
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 0
  ]

abbrev PositiveTerm := Fin 8
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
noncomputable def positiveFloor : ℝ := 226784787 / 1000000000000
noncomputable def negativeCeiling : ℝ := 0 / 1

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 42702622273724505638014287872, coefficient := 42702622273724505638014287872 }, { argument := 545325488810441210963788038144, coefficient := 545325488810441210963788038144 }, { argument := 42625421026462552678060785664, coefficient := 42625421026462552678060785664 }, { argument := 1577081510619146715565916160, coefficient := 1577081510619146715565916160 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 1544723855478523906561671168, coefficient := 1544723855478523906561671168 }, { argument := 77690503319044186676221968384, coefficient := 77690503319044186676221968384 }, { argument := 77659137360864966492712599552, coefficient := 77659137360864966492712599552 }, { argument := 1561960493140998111591661568, coefficient := 1561960493140998111591661568 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch2.Chunk4
