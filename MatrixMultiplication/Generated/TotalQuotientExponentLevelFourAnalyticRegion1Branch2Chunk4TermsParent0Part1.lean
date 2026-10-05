import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 4, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4737074185212841396984256984514560)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1936476927, 765261077327045, 32150704015946555, 47121457075, 41736147695, 1953520977595,
    531799301275, 16075357750762395, 1953520977595, 47121457075, 47121457075, 20194910175,
    47121457075, 531799301275, 20194910175, 382624795874405, 41736147695, 1767,
    21147, 31635, 9177, 1767, 36651, 18411,
    1767, 21147, 1767, 456601059, 38395236893, 19197613815,
    228305161, 81859410212325, 6661711729792111, 38685387663, 64655566105640885, 39696770347,
    1264228355, 38685387663, 21997573377, 39696770347, 619724739621, 758537013,
    3330858123812873, 38685387663, 1264228355, 758537013, 1264228355, 19469116667,
    21997573377, 81859410212325, 14541435, 1222778245, 611388975, 7270865,
    479535, 35412405, 369097575, 35412405, 479535, 14252627394063,
    4371, 249239557192749, 108159, 3441
  ]
def negativeCoefficients : Array ℕ := #[
    17860847138506267001949782016, 430803687836403023389696983040, 18099237328239501798128389980160, 217309364760703818122710220800, 192474008788051953194400481280, 9009025379079464002744358010880,
    2452491402299371661670586777600, 18099243794045234208213282324480, 9009025379079464002744358010880, 217309364760703818122710220800, 217309364760703818122710220800, 186265169794888986962323046400,
    217309364760703818122710220800, 2452491402299371661670586777600, 186265169794888986962323046400, 430797222030670613304804638720, 192474008788051953194400481280, 16688843150461326185201664,
    399455536052977549336117248, 298784127371162452670545920, 346697257706357873008705536, 16688843150461326185201664, 346158907927310733454344192, 347773957264452152117428224,
    16688843150461326185201664, 399455536052977549336117248, 16688843150461326185201664, 2105700719789438831570190336, 177066777153655521893282742272, 177066734435607933200388587520,
    2105743437837027524464345088, 23041375583062215303050035200, 1875105153996338339761478434816, 178404861402900462682717028352, 18198923963799547556364088770560, 183069040785982827720173682688,
    5830224228852956296820817920, 178404861402900462682717028352, 101445901582041439564682231808, 183069040785982827720173682688, 2857975916983719176701564944384, 111940305193976760898959704064,
    1875106425653455534004818149376, 178404861402900462682717028352, 5830224228852956296820817920, 111940305193976760898959704064, 5830224228852956296820817920, 179570906248671053942081191936,
    101445901582041439564682231808, 23041375583062215303050035200, 67060532477370663425802240, 5639069336103679041187348480, 5639067975656303605107916800, 67061892924746099505233920,
    141533750710180957346856960, 20903794306225679814214287360, 217876752136058136185693798400, 20903794306225679814214287360, 141533750710180957346856960, 4011757963809540640843235328,
    20641463896623219229065216, 140309397112406477810788466688, 510766436420697956668145664, 16249663067554449180327936
  ]
def negativeScales : Array ℕ := #[
    30, 49, 54, 35, 35, 40,
    38, 53, 40, 35, 35, 34,
    35, 38, 34, 48, 35, 10,
    14, 14, 13, 10, 15, 14,
    10, 14, 10, 28, 35, 34,
    27, 46, 52, 35, 55, 35,
    30, 35, 34, 35, 39, 29,
    51, 35, 30, 29, 30, 34,
    34, 46, 23, 30, 29, 22,
    18, 25, 28, 25, 18, 43,
    12, 47, 16, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30850787167593175, 49442945351663292, 54835699848642850, 35455665099297910, 35280578392739762, 40829213887578220,
    38952090936215555, 53835700364033873, 40829213887578220, 35455665099297910, 35455665099297910, 34233272677961405,
    35455665099297910, 38952090936215555, 34233272677961405, 48442923698515625, 35280578392739762, 10787086325046961,
    14368165390785547, 14949233985692235, 13163806892279359, 10787086325046961, 15161564941492690, 14168280368858667,
    10787086325046961, 14368165390785547, 10787086325046961, 28766358965044524, 35160208297917340, 34160207949861517,
    27766388232494610, 46218213505901620, 52564814349375583, 35171069679919410, 55843624094674806, 35208302586118385,
    30235609932114120, 35171069679919410, 34356625333075487, 35208302586118385, 39172836606093598, 29498644337948173,
    51564815327780870, 35171069679919410, 30235609932114120, 29498644337948173, 30235609932114120, 34180468377921659,
    34356625333075487, 46218213505901620, 23793666311287512, 30187515643913075, 29187515295857252, 22793695578737739,
    18871276594630224, 25077751490537107, 28459427018094118, 25077751490537107, 18871276594630224, 43696293130351843,
    12093747662785669, 47824526388358459, 16722794192703879, 11748612176955137
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
noncomputable def negativeCeiling : ℝ := 1654331313 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 17860847138506267001949782016, coefficient := (-17860847138506267001949782016) }, { argument := 430803687836403023389696983040, coefficient := (-430803687836403023389696983040) }, { argument := 18099237328239501798128389980160, coefficient := (-18099237328239501798128389980160) }, { argument := 217309364760703818122710220800, coefficient := (-217309364760703818122710220800) }, { argument := 192474008788051953194400481280, coefficient := (-192474008788051953194400481280) }, { argument := 9009025379079464002744358010880, coefficient := (-9009025379079464002744358010880) }, { argument := 2452491402299371661670586777600, coefficient := (-2452491402299371661670586777600) }, { argument := 18099243794045234208213282324480, coefficient := (-18099243794045234208213282324480) }, { argument := 9009025379079464002744358010880, coefficient := (-9009025379079464002744358010880) }, { argument := 217309364760703818122710220800, coefficient := (-217309364760703818122710220800) }, { argument := 217309364760703818122710220800, coefficient := (-217309364760703818122710220800) }, { argument := 186265169794888986962323046400, coefficient := (-186265169794888986962323046400) }, { argument := 217309364760703818122710220800, coefficient := (-217309364760703818122710220800) }, { argument := 2452491402299371661670586777600, coefficient := (-2452491402299371661670586777600) }, { argument := 186265169794888986962323046400, coefficient := (-186265169794888986962323046400) }, { argument := 430797222030670613304804638720, coefficient := (-430797222030670613304804638720) }, { argument := 192474008788051953194400481280, coefficient := (-192474008788051953194400481280) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 399455536052977549336117248, coefficient := (-399455536052977549336117248) }, { argument := 298784127371162452670545920, coefficient := (-298784127371162452670545920) }, { argument := 346697257706357873008705536, coefficient := (-346697257706357873008705536) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 346158907927310733454344192, coefficient := (-346158907927310733454344192) }, { argument := 347773957264452152117428224, coefficient := (-347773957264452152117428224) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 399455536052977549336117248, coefficient := (-399455536052977549336117248) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 2105700719789438831570190336, coefficient := (-2105700719789438831570190336) }, { argument := 177066777153655521893282742272, coefficient := (-177066777153655521893282742272) }, { argument := 177066734435607933200388587520, coefficient := (-177066734435607933200388587520) }, { argument := 2105743437837027524464345088, coefficient := (-2105743437837027524464345088) }, { argument := 23041375583062215303050035200, coefficient := (-23041375583062215303050035200) }, { argument := 1875105153996338339761478434816, coefficient := (-1875105153996338339761478434816) }, { argument := 178404861402900462682717028352, coefficient := (-178404861402900462682717028352) }, { argument := 18198923963799547556364088770560, coefficient := (-18198923963799547556364088770560) }, { argument := 183069040785982827720173682688, coefficient := (-183069040785982827720173682688) }, { argument := 5830224228852956296820817920, coefficient := (-5830224228852956296820817920) }, { argument := 178404861402900462682717028352, coefficient := (-178404861402900462682717028352) }, { argument := 101445901582041439564682231808, coefficient := (-101445901582041439564682231808) }, { argument := 183069040785982827720173682688, coefficient := (-183069040785982827720173682688) }, { argument := 2857975916983719176701564944384, coefficient := (-2857975916983719176701564944384) }, { argument := 111940305193976760898959704064, coefficient := (-111940305193976760898959704064) }, { argument := 1875106425653455534004818149376, coefficient := (-1875106425653455534004818149376) }, { argument := 178404861402900462682717028352, coefficient := (-178404861402900462682717028352) }, { argument := 5830224228852956296820817920, coefficient := (-5830224228852956296820817920) }, { argument := 111940305193976760898959704064, coefficient := (-111940305193976760898959704064) }, { argument := 5830224228852956296820817920, coefficient := (-5830224228852956296820817920) }, { argument := 179570906248671053942081191936, coefficient := (-179570906248671053942081191936) }, { argument := 101445901582041439564682231808, coefficient := (-101445901582041439564682231808) }, { argument := 23041375583062215303050035200, coefficient := (-23041375583062215303050035200) }, { argument := 67060532477370663425802240, coefficient := (-67060532477370663425802240) }, { argument := 5639069336103679041187348480, coefficient := (-5639069336103679041187348480) }, { argument := 5639067975656303605107916800, coefficient := (-5639067975656303605107916800) }, { argument := 67061892924746099505233920, coefficient := (-67061892924746099505233920) }, { argument := 141533750710180957346856960, coefficient := (-141533750710180957346856960) }, { argument := 20903794306225679814214287360, coefficient := (-20903794306225679814214287360) }, { argument := 217876752136058136185693798400, coefficient := (-217876752136058136185693798400) }, { argument := 20903794306225679814214287360, coefficient := (-20903794306225679814214287360) }, { argument := 141533750710180957346856960, coefficient := (-141533750710180957346856960) }, { argument := 4011757963809540640843235328, coefficient := (-4011757963809540640843235328) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 140309397112406477810788466688, coefficient := (-140309397112406477810788466688) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }] }

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


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-65220466920459217940153081266176)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    249239675412315, 1767, 1767, 59799, 3255, 108159,
    59799, 14252497193697, 3441, 3255, 4371, 1767,
    21147, 31635, 9177, 1767, 36651, 18411,
    1767, 21147, 1767, 59799, 715659, 1070595,
    310569, 59799, 1240347, 623067, 59799, 715659,
    59799, 444967911, 37417014297, 18708502635, 222488469, 3255,
    38955, 58275, 16905, 3255, 67515, 33915,
    3255, 38955, 3255, 253020969, 21276341463, 10638168165,
    126513051, 424731, 31365273, 326914995, 31365273, 424731,
    108159, 1294419, 1936395, 561729, 108159, 2243427,
    1126947, 108159, 1294419, 108159
  ]
def negativeCoefficients : Array ℕ := #[
    140309463664105650998508257280, 16688843150461326185201664, 16688843150461326185201664, 282392793309121914133807104, 15371302901740695170580480, 510766436420697956668145664,
    282392793309121914133807104, 4011721315664553071955935232, 16249663067554449180327936, 15371302901740695170580480, 20641463896623219229065216, 16688843150461326185201664,
    399455536052977549336117248, 298784127371162452670545920, 346697257706357873008705536, 16688843150461326185201664, 346158907927310733454344192, 347773957264452152117428224,
    16688843150461326185201664, 399455536052977549336117248, 16688843150461326185201664, 282392793309121914133807104, 6759208149528014847976931328, 5055741944727827817556869120,
    5866482544873371377489412096, 282392793309121914133807104, 5857373099927915831872192512, 5884701434764282468723851264, 282392793309121914133807104, 6759208149528014847976931328,
    282392793309121914133807104, 2052052293807542300829548544, 172555521684772578660332863488, 172555480055082890316302254080, 2052093923497230644860157952, 15371302901740695170580480,
    367919572680374058599055360, 275195906789228574828134400, 319326421571645409350123520, 15371302901740695170580480, 318830573090944096602685440, 320318118533048034844999680,
    15371302901740695170580480, 367919572680374058599055360, 15371302901740695170580480, 1166853265106249543608958976, 98119806448204015316659863552, 98119782776419682728877752320,
    1166876936890582131391070208, 125358464914731705078644736, 18514789242657030692589797376, 192976551891937206335900221440, 18514789242657030692589797376, 125358464914731705078644736,
    510766436420697956668145664, 12225441800779286575734325248, 9144366845596366643574865920, 10610760808223531744976961536, 510766436420697956668145664, 10594284471564799552826376192,
    10643713481540996129278132224, 510766436420697956668145664, 12225441800779286575734325248, 510766436420697956668145664
  ]
def negativeScales : Array ℕ := #[
    47, 10, 10, 15, 11, 16,
    15, 43, 11, 11, 12, 10,
    14, 14, 13, 10, 15, 14,
    10, 14, 10, 15, 19, 20,
    18, 15, 20, 19, 15, 19,
    15, 28, 35, 34, 27, 11,
    15, 15, 14, 11, 16, 15,
    11, 15, 11, 27, 34, 33,
    26, 18, 24, 28, 24, 18,
    16, 20, 20, 19, 16, 21,
    20, 16, 20, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    47824527072658923, 10787086325046961, 10787086325046961, 15867833740861174, 11668441828086828, 16722794192703879,
    15867833740861174, 43696279951007752, 11748612176955137, 11668441828086828, 12093747662785669, 10787086325046961,
    14368165390785547, 14949233985692235, 13163806892279359, 10787086325046961, 15161564941492690, 14168280368858667,
    10787086325046961, 14368165390785547, 10787086325046961, 15867833740861174, 19448912804669952, 20029981389286572,
    18244554306163721, 15867833740861174, 20242312355377051, 19249027782743029, 15867833740861174, 19448912804669952,
    15867833740861174, 28729126058666865, 35122975391718365, 34122975043662542, 27729155326116844, 11668441828086828,
    15249520894286927, 15830589480093830, 14045162395780740, 11668441828086828, 16042920444994070, 15049635872360048,
    11668441828086828, 15249520894286927, 11668441828086828, 27914681717350857, 34308531044874441, 33308530696818618,
    26914710984803665, 18696189885552550, 24902664788559998, 28284340311535961, 24902664788559998, 18696189885552550,
    16722794192703879, 20303873258815179, 20884941846757732, 19099514760308992, 16722794192703879, 21097272809522322,
    20103988236888300, 16722794192703879, 20303873258815179, 16722794192703879
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
noncomputable def negativeCeiling : ℝ := 411634487 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 140309463664105650998508257280, coefficient := (-140309463664105650998508257280) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 4011721315664553071955935232, coefficient := (-4011721315664553071955935232) }, { argument := 16249663067554449180327936, coefficient := (-16249663067554449180327936) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 20641463896623219229065216, coefficient := (-20641463896623219229065216) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 399455536052977549336117248, coefficient := (-399455536052977549336117248) }, { argument := 298784127371162452670545920, coefficient := (-298784127371162452670545920) }, { argument := 346697257706357873008705536, coefficient := (-346697257706357873008705536) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 346158907927310733454344192, coefficient := (-346158907927310733454344192) }, { argument := 347773957264452152117428224, coefficient := (-347773957264452152117428224) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 399455536052977549336117248, coefficient := (-399455536052977549336117248) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 6759208149528014847976931328, coefficient := (-6759208149528014847976931328) }, { argument := 5055741944727827817556869120, coefficient := (-5055741944727827817556869120) }, { argument := 5866482544873371377489412096, coefficient := (-5866482544873371377489412096) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 5857373099927915831872192512, coefficient := (-5857373099927915831872192512) }, { argument := 5884701434764282468723851264, coefficient := (-5884701434764282468723851264) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 6759208149528014847976931328, coefficient := (-6759208149528014847976931328) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 2052052293807542300829548544, coefficient := (-2052052293807542300829548544) }, { argument := 172555521684772578660332863488, coefficient := (-172555521684772578660332863488) }, { argument := 172555480055082890316302254080, coefficient := (-172555480055082890316302254080) }, { argument := 2052093923497230644860157952, coefficient := (-2052093923497230644860157952) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 275195906789228574828134400, coefficient := (-275195906789228574828134400) }, { argument := 319326421571645409350123520, coefficient := (-319326421571645409350123520) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 318830573090944096602685440, coefficient := (-318830573090944096602685440) }, { argument := 320318118533048034844999680, coefficient := (-320318118533048034844999680) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 1166853265106249543608958976, coefficient := (-1166853265106249543608958976) }, { argument := 98119806448204015316659863552, coefficient := (-98119806448204015316659863552) }, { argument := 98119782776419682728877752320, coefficient := (-98119782776419682728877752320) }, { argument := 1166876936890582131391070208, coefficient := (-1166876936890582131391070208) }, { argument := 125358464914731705078644736, coefficient := (-125358464914731705078644736) }, { argument := 18514789242657030692589797376, coefficient := (-18514789242657030692589797376) }, { argument := 192976551891937206335900221440, coefficient := (-192976551891937206335900221440) }, { argument := 18514789242657030692589797376, coefficient := (-18514789242657030692589797376) }, { argument := 125358464914731705078644736, coefficient := (-125358464914731705078644736) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 12225441800779286575734325248, coefficient := (-12225441800779286575734325248) }, { argument := 9144366845596366643574865920, coefficient := (-9144366845596366643574865920) }, { argument := 10610760808223531744976961536, coefficient := (-10610760808223531744976961536) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 10594284471564799552826376192, coefficient := (-10594284471564799552826376192) }, { argument := 10643713481540996129278132224, coefficient := (-10643713481540996129278132224) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }, { argument := 12225441800779286575734325248, coefficient := (-12225441800779286575734325248) }, { argument := 510766436420697956668145664, coefficient := (-510766436420697956668145664) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk4
