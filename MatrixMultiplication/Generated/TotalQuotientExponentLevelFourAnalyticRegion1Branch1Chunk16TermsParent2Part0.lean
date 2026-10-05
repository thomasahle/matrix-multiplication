import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 16, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-190540253234949119985280106889216)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    92753, 92753, 92753, 92753, 116697297, 2362124055,
    2657160087, 997061685, 97504455, 997061685, 1990978065, 116799735,
    2362124055, 97504455, 43717029, 1975930179, 5493795, 82946511,
    3276393201, 1596741, 4117911, 3445599, 96392733, 818762241,
    3445599, 3109443, 1596741, 1596741, 3109443, 96392733,
    3109443, 20736531, 4117911, 10841025, 10841025, 10841025,
    10841025, 1910129517, 46067778165, 35289096987, 19445387055, 1901599365,
    19445387055, 38829432195, 1910175045, 46067778165, 1901599365, 457429401,
    20674976751, 57483855, 7904512737, 54141134319, 754898139, 1946842569,
    1628990721, 45572008707, 6747776775, 1628990721, 1470064797, 754898139,
    754898139, 1470064797, 45572008707, 1470064797
  ]
def negativeCoefficients : Array ℕ := #[
    3504109267084865620047560704, 3504109267084865620047560704, 3504109267084865620047560704, 3504109267084865620047560704, 269085646481584179583647744, 5446687239117253119427215360,
    6126994010970600823087693824, 4598135432224152433710858240, 224829965928941207326556160, 4598135432224152433710858240, 4590882852678057556055162880, 269321852427762011964702720,
    5446687239117253119427215360, 224829965928941207326556160, 50402302851621162848354304, 2278092394970756469913288704, 50671315179212583060111360, 191261632528016766740201472,
    7554848357961127220427620352, 117818690315996252627533824, 151924100670626746809188352, 2033922653876145834833215488, 3556264152432834256941613056, 7551748758471950832110665728,
    2033922653876145834833215488, 114718198465575298611019776, 117818690315996252627533824, 117818690315996252627533824, 114718198465575298611019776, 3556264152432834256941613056,
    114718198465575298611019776, 191260740166772201040642048, 151924100670626746809188352, 12798823274987973875702169600, 12798823274987973875702169600, 12798823274987973875702169600,
    12798823274987973875702169600, 8808917586934359556639162368, 212450128463545008121876316160, 162742235177875960961326645248, 179352039208904840411810365440, 8769579204220899136855080960,
    179352039208904840411810365440, 179069149557155779149331169280, 8809127547775406518755655680, 212450128463545008121876316160, 8769579204220899136855080960, 527380193252328752730341376,
    23836625303474500624214654976, 530194980777614588604579840, 18226565435852052198403866624, 124840956080365758829389938688, 13925412771852619341442842624, 17956453311073114413965770752,
    240396599429876797052276441088, 420327590771446168016708960256, 124474511234946200490108518400, 240396599429876797052276441088, 13558954541014392516668030976, 13925412771852619341442842624,
    13925412771852619341442842624, 13558954541014392516668030976, 420327590771446168016708960256, 13558954541014392516668030976
  ]
def negativeScales : Array ℕ := #[
    16, 16, 16, 16, 26, 31,
    31, 29, 26, 29, 30, 26,
    31, 26, 25, 30, 22, 26,
    31, 20, 21, 21, 26, 29,
    21, 21, 20, 20, 21, 26,
    21, 24, 21, 23, 23, 23,
    23, 30, 35, 35, 34, 30,
    34, 35, 30, 35, 30, 28,
    34, 25, 32, 35, 29, 30,
    30, 35, 32, 30, 30, 29,
    29, 30, 35, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16501106324519055, 16501106324519055, 16501106324519055, 16501106324519055, 26798195904744064, 31137437588760922,
    31307238003065566, 29893107525243961, 26538964801634474, 29893107525243961, 30890830184377055, 26799461760714204,
    31137437588760922, 26538964801634474, 25381692023304400, 30879884826111423, 22389371646829086, 26305677962223776,
    31609461359657599, 20606698888142346, 21973481234220725, 21716323379415823, 26522421050708350, 29608869329984609,
    21716323379415823, 21568224740323199, 20606698888142346, 20606698888142346, 21568224740323199, 26522421050708350,
    21568224740323199, 24305671231087330, 21973481234220725, 23369997831651248, 23369997831651248, 23369997831651248,
    23369997831651248, 30831023319206119, 35423038967748402, 35038503462328038, 34178708900373521, 30824566181678358,
    34178708900373521, 35176431559662455, 30831057705480983, 35423038967748402, 30824566181678358, 28768973856524418,
    34267166655961305, 25776653480108848, 32880029389365385, 35656006062887452, 29491706748869745, 30858489081576191,
    30601331240049905, 35407428911441788, 32651765102244681, 30601331240049905, 30453232601054957, 29491706748869745,
    29491706748869745, 30453232601054957, 35407428911441788, 30453232601054957
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
noncomputable def negativeCeiling : ℝ := 1217010057 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3504109267084865620047560704, coefficient := (-3504109267084865620047560704) }, { argument := 3504109267084865620047560704, coefficient := (-3504109267084865620047560704) }, { argument := 3504109267084865620047560704, coefficient := (-3504109267084865620047560704) }, { argument := 3504109267084865620047560704, coefficient := (-3504109267084865620047560704) }, { argument := 269085646481584179583647744, coefficient := (-269085646481584179583647744) }, { argument := 5446687239117253119427215360, coefficient := (-5446687239117253119427215360) }, { argument := 6126994010970600823087693824, coefficient := (-6126994010970600823087693824) }, { argument := 4598135432224152433710858240, coefficient := (-4598135432224152433710858240) }, { argument := 224829965928941207326556160, coefficient := (-224829965928941207326556160) }, { argument := 4598135432224152433710858240, coefficient := (-4598135432224152433710858240) }, { argument := 4590882852678057556055162880, coefficient := (-4590882852678057556055162880) }, { argument := 269321852427762011964702720, coefficient := (-269321852427762011964702720) }, { argument := 5446687239117253119427215360, coefficient := (-5446687239117253119427215360) }, { argument := 224829965928941207326556160, coefficient := (-224829965928941207326556160) }, { argument := 50402302851621162848354304, coefficient := (-50402302851621162848354304) }, { argument := 2278092394970756469913288704, coefficient := (-2278092394970756469913288704) }, { argument := 50671315179212583060111360, coefficient := (-50671315179212583060111360) }, { argument := 191261632528016766740201472, coefficient := (-191261632528016766740201472) }, { argument := 7554848357961127220427620352, coefficient := (-7554848357961127220427620352) }, { argument := 117818690315996252627533824, coefficient := (-117818690315996252627533824) }, { argument := 151924100670626746809188352, coefficient := (-151924100670626746809188352) }, { argument := 2033922653876145834833215488, coefficient := (-2033922653876145834833215488) }, { argument := 3556264152432834256941613056, coefficient := (-3556264152432834256941613056) }, { argument := 7551748758471950832110665728, coefficient := (-7551748758471950832110665728) }, { argument := 2033922653876145834833215488, coefficient := (-2033922653876145834833215488) }, { argument := 114718198465575298611019776, coefficient := (-114718198465575298611019776) }, { argument := 117818690315996252627533824, coefficient := (-117818690315996252627533824) }, { argument := 117818690315996252627533824, coefficient := (-117818690315996252627533824) }, { argument := 114718198465575298611019776, coefficient := (-114718198465575298611019776) }, { argument := 3556264152432834256941613056, coefficient := (-3556264152432834256941613056) }, { argument := 114718198465575298611019776, coefficient := (-114718198465575298611019776) }, { argument := 191260740166772201040642048, coefficient := (-191260740166772201040642048) }, { argument := 151924100670626746809188352, coefficient := (-151924100670626746809188352) }, { argument := 12798823274987973875702169600, coefficient := (-12798823274987973875702169600) }, { argument := 12798823274987973875702169600, coefficient := (-12798823274987973875702169600) }, { argument := 12798823274987973875702169600, coefficient := (-12798823274987973875702169600) }, { argument := 12798823274987973875702169600, coefficient := (-12798823274987973875702169600) }, { argument := 8808917586934359556639162368, coefficient := (-8808917586934359556639162368) }, { argument := 212450128463545008121876316160, coefficient := (-212450128463545008121876316160) }, { argument := 162742235177875960961326645248, coefficient := (-162742235177875960961326645248) }, { argument := 179352039208904840411810365440, coefficient := (-179352039208904840411810365440) }, { argument := 8769579204220899136855080960, coefficient := (-8769579204220899136855080960) }, { argument := 179352039208904840411810365440, coefficient := (-179352039208904840411810365440) }, { argument := 179069149557155779149331169280, coefficient := (-179069149557155779149331169280) }, { argument := 8809127547775406518755655680, coefficient := (-8809127547775406518755655680) }, { argument := 212450128463545008121876316160, coefficient := (-212450128463545008121876316160) }, { argument := 8769579204220899136855080960, coefficient := (-8769579204220899136855080960) }, { argument := 527380193252328752730341376, coefficient := (-527380193252328752730341376) }, { argument := 23836625303474500624214654976, coefficient := (-23836625303474500624214654976) }, { argument := 530194980777614588604579840, coefficient := (-530194980777614588604579840) }, { argument := 18226565435852052198403866624, coefficient := (-18226565435852052198403866624) }, { argument := 124840956080365758829389938688, coefficient := (-124840956080365758829389938688) }, { argument := 13925412771852619341442842624, coefficient := (-13925412771852619341442842624) }, { argument := 17956453311073114413965770752, coefficient := (-17956453311073114413965770752) }, { argument := 240396599429876797052276441088, coefficient := (-240396599429876797052276441088) }, { argument := 420327590771446168016708960256, coefficient := (-420327590771446168016708960256) }, { argument := 124474511234946200490108518400, coefficient := (-124474511234946200490108518400) }, { argument := 240396599429876797052276441088, coefficient := (-240396599429876797052276441088) }, { argument := 13558954541014392516668030976, coefficient := (-13558954541014392516668030976) }, { argument := 13925412771852619341442842624, coefficient := (-13925412771852619341442842624) }, { argument := 13925412771852619341442842624, coefficient := (-13925412771852619341442842624) }, { argument := 13558954541014392516668030976, coefficient := (-13558954541014392516668030976) }, { argument := 420327590771446168016708960256, coefficient := (-420327590771446168016708960256) }, { argument := 13558954541014392516668030976, coefficient := (-13558954541014392516668030976) }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1017466983106198544163914970562560)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1976126733, 1946842569, 20259111, 915674961, 2545905, 484653387,
    85003650741, 21250915233, 121160799, 81762255, 7764541281, 484653387,
    71082519615, 153371325, 18404559, 484653387, 963171921, 153371325,
    14864748819, 950902215, 7764546417, 484653387, 18404559, 950902215,
    18404559, 484653387, 484653387, 81762255, 2968095, 2968095,
    2968095, 2968095, 3820257639, 92135522535, 70578168369, 38890759845,
    3803197335, 38890759845, 77658835905, 3820348695, 92135522535, 3803197335,
    72410820831, 57522298941, 28655331441, 73900591611, 61835188899, 1729877113833,
    56014123989, 61835188899, 55802487543, 28655331441, 28655331441, 55802487543,
    1729877113833, 55802487543, 18102705111, 73900591611, 20259111, 915674961,
    2545905, 153371325, 26899889475, 6724973175
  ]
def negativeCoefficients : Array ℕ := #[
    18226552050433383712910475264, 17956453311073114413965770752, 46714329472234248493596672, 2111402707533871850163535872, 46963657970977516006932480, 1117534624305688980618215424,
    196005073818777285730272018432, 196005097317623392627027083264, 1117511125459582083863150592, 188530924109297394395381760, 17903813232544990040804032512, 1117534624305688980618215424,
    163905130931543026069646868480, 707300395130182899125452800, 42438023707810973947527168, 1117534624305688980618215424, 1110461620354387151626960896, 707300395130182899125452800,
    17137888574004331645809721344, 1096315612451783493644451840, 17903825075354685362336169984, 1117534624305688980618215424, 42438023707810973947527168, 1096315612451783493644451840,
    42438023707810973947527168, 1117534624305688980618215424, 1117534624305688980618215424, 188530924109297394395381760, 3504108086493244902636257280, 3504108086493244902636257280,
    3504108086493244902636257280, 3504108086493244902636257280, 8808914370283361703536099328, 212450050537580511745089208320, 162742176136765710044693004288, 179351973423203787545121914880,
    8769575987569901283752017920, 179351973423203787545121914880, 179069083875217661697258946560, 8809124331124408665652592640, 212450050537580511745089208320, 8769575987569901283752017920,
    166967985004586674949940314112, 132637390887005120857827704832, 132149391359862433980994289664, 170403162542980506975492636672, 2281315808738677807671901421568, 3988825049730584520426327638016,
    129159776217264722424027414528, 2281315808738677807671901421568, 128671775797760790981494439936, 132149391359862433980994289664, 132149391359862433980994289664, 128671775797760790981494439936,
    3988825049730584520426327638016, 128671775797760790981494439936, 166967984112225430384240754688, 170403162542980506975492636672, 46714329472234248493596672, 2111402707533871850163535872,
    46963657970977516006932480, 707300395130182899125452800, 124053844189099547930551910400, 124053859061786957358877900800
  ]
def negativeScales : Array ℕ := #[
    30, 30, 24, 29, 21, 28,
    36, 34, 26, 26, 32, 28,
    36, 27, 24, 28, 29, 27,
    33, 29, 32, 28, 24, 29,
    24, 28, 28, 26, 21, 21,
    21, 21, 31, 36, 36, 35,
    31, 35, 36, 31, 36, 31,
    36, 35, 34, 36, 35, 40,
    35, 35, 35, 34, 34, 35,
    40, 35, 34, 36, 24, 29,
    21, 27, 34, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30880028329863233, 30858489081576191, 24272067532129899, 29770260332253290, 21279747155654583, 28852378094544711,
    36306805752392587, 34306805925355797, 26852347758100888, 26284931650512196, 32854253550448075, 28852378094544711,
    36048775769402291, 27192453534329897, 24133559845276328, 28852378094544711, 29843218094967739, 27192453534329897,
    33791176034545603, 29824721750890029, 32854254504745215, 28852378094544711, 24133559845276328, 29824721750890029,
    24133559845276328, 28852378094544711, 28852378094544711, 26284931650512196, 21501105838451461, 21501105838451461,
    21501105838451461, 21501105838451461, 31831022792393675, 36423038438572807, 36038502938933897, 35178708371197926,
    31824565652502751, 35178708371197926, 36176431030486860, 31831057178681096, 36423038438572807, 31824565652502751,
    36075486253816416, 35743402284868021, 34738084532284110, 36104866862782796, 35847709024943575, 40653806694706879,
    35705071598262637, 35847709024943575, 35699610384368265, 34738084532284110, 34738084532284110, 35699610384368265,
    40653806694706879, 35699610384368265, 34075486246105925, 36104866862782796, 24272067532129899, 29770260332253290,
    21279747155654583, 27192453534329897, 34646881194009885, 32646881366973095
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
noncomputable def negativeCeiling : ℝ := 3744460423 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 18226552050433383712910475264, coefficient := (-18226552050433383712910475264) }, { argument := 17956453311073114413965770752, coefficient := (-17956453311073114413965770752) }, { argument := 46714329472234248493596672, coefficient := (-46714329472234248493596672) }, { argument := 2111402707533871850163535872, coefficient := (-2111402707533871850163535872) }, { argument := 46963657970977516006932480, coefficient := (-46963657970977516006932480) }, { argument := 1117534624305688980618215424, coefficient := (-1117534624305688980618215424) }, { argument := 196005073818777285730272018432, coefficient := (-196005073818777285730272018432) }, { argument := 196005097317623392627027083264, coefficient := (-196005097317623392627027083264) }, { argument := 1117511125459582083863150592, coefficient := (-1117511125459582083863150592) }, { argument := 188530924109297394395381760, coefficient := (-188530924109297394395381760) }, { argument := 17903813232544990040804032512, coefficient := (-17903813232544990040804032512) }, { argument := 1117534624305688980618215424, coefficient := (-1117534624305688980618215424) }, { argument := 163905130931543026069646868480, coefficient := (-163905130931543026069646868480) }, { argument := 707300395130182899125452800, coefficient := (-707300395130182899125452800) }, { argument := 42438023707810973947527168, coefficient := (-42438023707810973947527168) }, { argument := 1117534624305688980618215424, coefficient := (-1117534624305688980618215424) }, { argument := 1110461620354387151626960896, coefficient := (-1110461620354387151626960896) }, { argument := 707300395130182899125452800, coefficient := (-707300395130182899125452800) }, { argument := 17137888574004331645809721344, coefficient := (-17137888574004331645809721344) }, { argument := 1096315612451783493644451840, coefficient := (-1096315612451783493644451840) }, { argument := 17903825075354685362336169984, coefficient := (-17903825075354685362336169984) }, { argument := 1117534624305688980618215424, coefficient := (-1117534624305688980618215424) }, { argument := 42438023707810973947527168, coefficient := (-42438023707810973947527168) }, { argument := 1096315612451783493644451840, coefficient := (-1096315612451783493644451840) }, { argument := 42438023707810973947527168, coefficient := (-42438023707810973947527168) }, { argument := 1117534624305688980618215424, coefficient := (-1117534624305688980618215424) }, { argument := 1117534624305688980618215424, coefficient := (-1117534624305688980618215424) }, { argument := 188530924109297394395381760, coefficient := (-188530924109297394395381760) }, { argument := 3504108086493244902636257280, coefficient := (-3504108086493244902636257280) }, { argument := 3504108086493244902636257280, coefficient := (-3504108086493244902636257280) }, { argument := 3504108086493244902636257280, coefficient := (-3504108086493244902636257280) }, { argument := 3504108086493244902636257280, coefficient := (-3504108086493244902636257280) }, { argument := 8808914370283361703536099328, coefficient := (-8808914370283361703536099328) }, { argument := 212450050537580511745089208320, coefficient := (-212450050537580511745089208320) }, { argument := 162742176136765710044693004288, coefficient := (-162742176136765710044693004288) }, { argument := 179351973423203787545121914880, coefficient := (-179351973423203787545121914880) }, { argument := 8769575987569901283752017920, coefficient := (-8769575987569901283752017920) }, { argument := 179351973423203787545121914880, coefficient := (-179351973423203787545121914880) }, { argument := 179069083875217661697258946560, coefficient := (-179069083875217661697258946560) }, { argument := 8809124331124408665652592640, coefficient := (-8809124331124408665652592640) }, { argument := 212450050537580511745089208320, coefficient := (-212450050537580511745089208320) }, { argument := 8769575987569901283752017920, coefficient := (-8769575987569901283752017920) }, { argument := 166967985004586674949940314112, coefficient := (-166967985004586674949940314112) }, { argument := 132637390887005120857827704832, coefficient := (-132637390887005120857827704832) }, { argument := 132149391359862433980994289664, coefficient := (-132149391359862433980994289664) }, { argument := 170403162542980506975492636672, coefficient := (-170403162542980506975492636672) }, { argument := 2281315808738677807671901421568, coefficient := (-2281315808738677807671901421568) }, { argument := 3988825049730584520426327638016, coefficient := (-3988825049730584520426327638016) }, { argument := 129159776217264722424027414528, coefficient := (-129159776217264722424027414528) }, { argument := 2281315808738677807671901421568, coefficient := (-2281315808738677807671901421568) }, { argument := 128671775797760790981494439936, coefficient := (-128671775797760790981494439936) }, { argument := 132149391359862433980994289664, coefficient := (-132149391359862433980994289664) }, { argument := 132149391359862433980994289664, coefficient := (-132149391359862433980994289664) }, { argument := 128671775797760790981494439936, coefficient := (-128671775797760790981494439936) }, { argument := 3988825049730584520426327638016, coefficient := (-3988825049730584520426327638016) }, { argument := 128671775797760790981494439936, coefficient := (-128671775797760790981494439936) }, { argument := 166967984112225430384240754688, coefficient := (-166967984112225430384240754688) }, { argument := 170403162542980506975492636672, coefficient := (-170403162542980506975492636672) }, { argument := 46714329472234248493596672, coefficient := (-46714329472234248493596672) }, { argument := 2111402707533871850163535872, coefficient := (-2111402707533871850163535872) }, { argument := 46963657970977516006932480, coefficient := (-46963657970977516006932480) }, { argument := 707300395130182899125452800, coefficient := (-707300395130182899125452800) }, { argument := 124053844189099547930551910400, coefficient := (-124053844189099547930551910400) }, { argument := 124053859061786957358877900800, coefficient := (-124053859061786957358877900800) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16
