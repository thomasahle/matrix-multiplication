import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 13, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-34517495655029366277323846525648896)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    10666921, 710976599, 1065, 489, 20421, 14409,
    355488369, 20421, 1065, 531, 927, 531,
    14409, 927, 5333391, 489, 35647851622159, 4146483917439597,
    106339742955, 43305373635957631, 6605817875, 7029773015, 106339742955, 63432013035,
    6605817875, 1678239895155, 34603776285, 2073242782900731, 106339742955, 7029773015,
    34603776285, 7029773015, 106989860075, 63432013035, 35667002990607, 20188420489972971,
    7507535287, 366931669717999985, 185527276339, 5912505341, 366924730380699495, 3035966075,
    3035966075, 103098829163, 5593651723, 185527276339, 103098829163, 20202323039273317,
    5912505341, 5593651723, 7507535287, 285, 5415, 8265,
    85215, 2565, 8265, 2565, 2565, 219735,
    2565, 85215, 219735, 285
  ]
def negativeCoefficients : Array ℕ := #[
    100746220411636717585046700032, 6714984122444504228740420599808, 20600095966233281136993239040, 18917271225329717325802242048, 789999173195210956053594243072, 278710594157235068453460639744,
    6714985435262386466501790007296, 789999173195210956053594243072, 20600095966233281136993239040, 20542067526891778936607342592, 17930787756524179919242002432, 20542067526891778936607342592,
    278710594157235068453460639744, 17930787756524179919242002432, 100744907593754479823677292544, 18917271225329717325802242048, 160543651282114003769296420864, 18674103425478723549706019930112,
    245202752894367911521718108160, 195030064570038888470031395454976, 243711663475321747246415872000, 8104776481498411056119152640, 245202752894367911521718108160, 146264263817106659863764664320,
    243711663475321747246415872000, 3869757730026679436994737602560, 159581751278323718546931056640, 18674110849040604535441852465152, 245202752894367911521718108160, 8104776481498411056119152640,
    159581751278323718546931056640, 8104776481498411056119152640, 246701820910690051698353766400, 146264263817106659863764664320, 160629901377920051643596931072, 5682535187240072404595927678976,
    8655598878977036734129242112, 206564166376552330441980714680320, 213898386582370160467838500864, 6816654553741738850769698816, 206560259876942244823527000637440, 7000461150248687263704678400,
    7000461150248687263704678400, 118864857241810233858707161088, 6449041360727842024899739648, 213898386582370160467838500864, 118864857241810233858707161088, 5686448406980606041813210365952,
    6816654553741738850769698816, 6449041360727842024899739648, 8655598878977036734129242112, 344543858590169314791260160, 409145832075826061314621440, 312242871847340941529579520,
    3219331678701894535080837120, 387611840913940479140167680, 312242871847340941529579520, 387611840913940479140167680, 387611840913940479140167680, 16602707185813783856503848960,
    387611840913940479140167680, 3219331678701894535080837120, 16602707185813783856503848960, 344543858590169314791260160
  ]
def negativeScales : Array ℕ := #[
    23, 29, 10, 8, 14, 13,
    28, 14, 10, 9, 9, 9,
    13, 9, 22, 8, 45, 51,
    36, 55, 32, 32, 36, 35,
    32, 40, 35, 50, 36, 32,
    35, 32, 36, 35, 45, 54,
    32, 58, 37, 32, 58, 31,
    31, 36, 32, 37, 36, 54,
    32, 32, 32, 8, 12, 13,
    16, 11, 13, 11, 11, 17,
    11, 16, 17, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    23346640467452803, 29405226835030461, 10056637715113201, 8933690662845865, 14317765895114651, 13814682594827495,
    28405227117085583, 14317765895114651, 10056637715113201, 9052568050804154, 9856425530582692, 9052568050804154,
    13814682594827495, 9856425530582692, 22346621667658817, 8933690662845865, 45018880366377323, 51880809923099385,
    36629889928021026, 55265395574025877, 32621090048497665, 32710830960813879, 36629889928021026, 35884492079453095,
    32621090048497665, 40610086094488993, 35010210435590017, 50880810496617382, 36629889928021026, 32710830960813879,
    35010210435590017, 32710830960813879, 36638683115985480, 35884492079453095, 45019655228363662, 54164377559108707,
    32805692205480942, 58348289041447351, 37432840352149570, 32461122435682463, 58348261757233411, 31499508523625706,
    31499508523625706, 36585236992665460, 32381143284213908, 37432840352149570, 36585236992665460, 54165370714370080,
    32461122435682463, 32381143284213908, 32805692205480942, 8154818109052105, 12402745622495697, 13012799104179677,
    16378819783250212, 11324743110494417, 13012799104179677, 11324743110494417, 11324743110494417, 17745405159170467,
    11324743110494417, 16378819783250212, 17745405159170467, 8154818109052105
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
noncomputable def negativeCeiling : ℝ := 458806646981 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 100746220411636717585046700032, coefficient := (-100746220411636717585046700032) }, { argument := 6714984122444504228740420599808, coefficient := (-6714984122444504228740420599808) }, { argument := 20600095966233281136993239040, coefficient := (-20600095966233281136993239040) }, { argument := 18917271225329717325802242048, coefficient := (-18917271225329717325802242048) }, { argument := 789999173195210956053594243072, coefficient := (-789999173195210956053594243072) }, { argument := 278710594157235068453460639744, coefficient := (-278710594157235068453460639744) }, { argument := 6714985435262386466501790007296, coefficient := (-6714985435262386466501790007296) }, { argument := 789999173195210956053594243072, coefficient := (-789999173195210956053594243072) }, { argument := 20600095966233281136993239040, coefficient := (-20600095966233281136993239040) }, { argument := 20542067526891778936607342592, coefficient := (-20542067526891778936607342592) }, { argument := 17930787756524179919242002432, coefficient := (-17930787756524179919242002432) }, { argument := 20542067526891778936607342592, coefficient := (-20542067526891778936607342592) }, { argument := 278710594157235068453460639744, coefficient := (-278710594157235068453460639744) }, { argument := 17930787756524179919242002432, coefficient := (-17930787756524179919242002432) }, { argument := 100744907593754479823677292544, coefficient := (-100744907593754479823677292544) }, { argument := 18917271225329717325802242048, coefficient := (-18917271225329717325802242048) }, { argument := 160543651282114003769296420864, coefficient := (-160543651282114003769296420864) }, { argument := 18674103425478723549706019930112, coefficient := (-18674103425478723549706019930112) }, { argument := 245202752894367911521718108160, coefficient := (-245202752894367911521718108160) }, { argument := 195030064570038888470031395454976, coefficient := (-195030064570038888470031395454976) }, { argument := 243711663475321747246415872000, coefficient := (-243711663475321747246415872000) }, { argument := 8104776481498411056119152640, coefficient := (-8104776481498411056119152640) }, { argument := 245202752894367911521718108160, coefficient := (-245202752894367911521718108160) }, { argument := 146264263817106659863764664320, coefficient := (-146264263817106659863764664320) }, { argument := 243711663475321747246415872000, coefficient := (-243711663475321747246415872000) }, { argument := 3869757730026679436994737602560, coefficient := (-3869757730026679436994737602560) }, { argument := 159581751278323718546931056640, coefficient := (-159581751278323718546931056640) }, { argument := 18674110849040604535441852465152, coefficient := (-18674110849040604535441852465152) }, { argument := 245202752894367911521718108160, coefficient := (-245202752894367911521718108160) }, { argument := 8104776481498411056119152640, coefficient := (-8104776481498411056119152640) }, { argument := 159581751278323718546931056640, coefficient := (-159581751278323718546931056640) }, { argument := 8104776481498411056119152640, coefficient := (-8104776481498411056119152640) }, { argument := 246701820910690051698353766400, coefficient := (-246701820910690051698353766400) }, { argument := 146264263817106659863764664320, coefficient := (-146264263817106659863764664320) }, { argument := 160629901377920051643596931072, coefficient := (-160629901377920051643596931072) }, { argument := 5682535187240072404595927678976, coefficient := (-5682535187240072404595927678976) }, { argument := 8655598878977036734129242112, coefficient := (-8655598878977036734129242112) }, { argument := 206564166376552330441980714680320, coefficient := (-206564166376552330441980714680320) }, { argument := 213898386582370160467838500864, coefficient := (-213898386582370160467838500864) }, { argument := 6816654553741738850769698816, coefficient := (-6816654553741738850769698816) }, { argument := 206560259876942244823527000637440, coefficient := (-206560259876942244823527000637440) }, { argument := 7000461150248687263704678400, coefficient := (-7000461150248687263704678400) }, { argument := 7000461150248687263704678400, coefficient := (-7000461150248687263704678400) }, { argument := 118864857241810233858707161088, coefficient := (-118864857241810233858707161088) }, { argument := 6449041360727842024899739648, coefficient := (-6449041360727842024899739648) }, { argument := 213898386582370160467838500864, coefficient := (-213898386582370160467838500864) }, { argument := 118864857241810233858707161088, coefficient := (-118864857241810233858707161088) }, { argument := 5686448406980606041813210365952, coefficient := (-5686448406980606041813210365952) }, { argument := 6816654553741738850769698816, coefficient := (-6816654553741738850769698816) }, { argument := 6449041360727842024899739648, coefficient := (-6449041360727842024899739648) }, { argument := 8655598878977036734129242112, coefficient := (-8655598878977036734129242112) }, { argument := 344543858590169314791260160, coefficient := (-344543858590169314791260160) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 312242871847340941529579520, coefficient := (-312242871847340941529579520) }, { argument := 3219331678701894535080837120, coefficient := (-3219331678701894535080837120) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 312242871847340941529579520, coefficient := (-312242871847340941529579520) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 16602707185813783856503848960, coefficient := (-16602707185813783856503848960) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 3219331678701894535080837120, coefficient := (-3219331678701894535080837120) }, { argument := 16602707185813783856503848960, coefficient := (-16602707185813783856503848960) }, { argument := 344543858590169314791260160, coefficient := (-344543858590169314791260160) }] }

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
def constantNumerator : ℤ := (-50632761675584799482637249819967488)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2565, 2565, 5415, 20091713979878359, 285, 93,
    34664011598980905, 939, 20091713877648855, 1881, 843, 285,
    93, 93, 1767, 2697, 27807, 837,
    2697, 837, 837, 71703, 837, 27807,
    71703, 93, 837, 837, 1767, 1841539199,
    5415, 1767, 6649399653, 17841, 460384647, 35739,
    16017, 5415, 1767, 284289556311211, 284289127912277, 35647798087921,
    4146482152783251, 106336635669, 43305362477034625, 6605715437, 7029533993, 106336635669,
    63428905749, 6605715437, 1678201549197, 34602239715, 2073241900572165, 106336635669,
    7029533993, 34602239715, 7029533993, 106986752789, 63428905749, 35666940714993,
    34829878652712477, 27103370829, 632739286612877579, 665644530273
  ]
def negativeCoefficients : Array ℕ := #[
    387611840913940479140167680, 387611840913940479140167680, 409145832075826061314621440, 5655314724563422672528819093504, 344543858590169314791260160, 14053762653020064155959296,
    19514103715042119372437308047360, 283795336154534198762274816, 5655314695788375414986904698880, 284248683336889684702789632, 254781116483783098569326592, 344543858590169314791260160,
    14053762653020064155959296, 14053762653020064155959296, 16688843150461326185201664, 12736222404299433141338112, 131314844789156224457244672, 15810482984647572175454208,
    12736222404299433141338112, 15810482984647572175454208, 15810482984647572175454208, 677215687842404341515288576, 15810482984647572175454208, 131314844789156224457244672,
    677215687842404341515288576, 14053762653020064155959296, 15810482984647572175454208, 15810482984647572175454208, 16688843150461326185201664, 8492600576414271160394448896,
    409145832075826061314621440, 16688843150461326185201664, 30664943410676024734553997312, 337006961683509361030201344, 8492597758674113901260439552, 337545311462556500584562688,
    302552575824492429551075328, 409145832075826061314621440, 16688843150461326185201664, 160040792483561687371671928832, 160040551316401746331958247424, 160543410185339695405849378816,
    18674095478173061267124960362496, 245195587980667183939492773888, 195030014314717396792376295424000, 243707884180182901928318992384, 8104500907894536918341255168, 245195587980667183939492773888,
    146257098903405932281539330048, 243707884180182901928318992384, 3869669310267493535073429356544, 159574665099938383575499407360, 18674102901731402423553679687680, 245195587980667183939492773888,
    8104500907894536918341255168, 159574665099938383575499407360, 8104500907894536918341255168, 246694655996989324116128432128, 146257098903405932281539330048, 160629620913488046974753046528,
    19607478565214438084595180109824, 31248059076088005442985263104, 712401103853107233228496931127296, 767435893375665060879110504448
  ]
def negativeScales : Array ℕ := #[
    11, 11, 12, 54, 8, 6,
    54, 9, 54, 10, 9, 8,
    6, 6, 10, 11, 14, 9,
    11, 9, 9, 16, 9, 14,
    16, 6, 9, 9, 10, 30,
    12, 10, 32, 14, 28, 15,
    13, 12, 10, 48, 48, 45,
    51, 36, 55, 32, 32, 36,
    35, 32, 40, 35, 50, 36,
    32, 35, 32, 36, 35, 45,
    54, 34, 59, 39
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11324743110494417, 11324743110494417, 12402745622495697, 54157450160656024, 8154818109052105, 6539158811108986,
    54944288152125364, 9874981350423323, 54157450153315386, 10877284136413052, 9719388821055554, 8154818109052105,
    6539158811108986, 6539158811108986, 10787086325046961, 11397139806235610, 14763160485605156, 9709083812639846,
    11397139806235610, 9709083812639846, 9709083812639846, 16129745861023066, 9709083812639846, 14763160485605156,
    16129745861023066, 6539158811108986, 9709083812639846, 9709083812639846, 10787086325046961, 30778264961166772,
    12402745622495697, 10787086325046961, 32630576945479504, 14122908861097361, 28778264482498263, 15125211646966781,
    13967316348309272, 12402745622495697, 10787086325046961, 48014354429426648, 48014352255412620, 45018878199805309,
    51880809309118553, 36629847771330813, 55265395202272360, 32621067676106642, 32710781906354133, 36629847771330813,
    35884421405735504, 32621067676106642, 40610053130098357, 35010146371739865, 50880809882636521, 36629847771330813,
    32710781906354133, 35010146371739865, 32710781906354133, 36638641215461447, 35884421405735504, 45019652709374389,
    54951174975414858, 34657753238702325, 59134388788267707, 39275960993849209
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
noncomputable def negativeCeiling : ℝ := 348359364139 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 387611840913940479140167680, coefficient := (-387611840913940479140167680) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 5655314724563422672528819093504, coefficient := (-5655314724563422672528819093504) }, { argument := 344543858590169314791260160, coefficient := (-344543858590169314791260160) }, { argument := 14053762653020064155959296, coefficient := (-14053762653020064155959296) }, { argument := 19514103715042119372437308047360, coefficient := (-19514103715042119372437308047360) }, { argument := 283795336154534198762274816, coefficient := (-283795336154534198762274816) }, { argument := 5655314695788375414986904698880, coefficient := (-5655314695788375414986904698880) }, { argument := 284248683336889684702789632, coefficient := (-284248683336889684702789632) }, { argument := 254781116483783098569326592, coefficient := (-254781116483783098569326592) }, { argument := 344543858590169314791260160, coefficient := (-344543858590169314791260160) }, { argument := 14053762653020064155959296, coefficient := (-14053762653020064155959296) }, { argument := 14053762653020064155959296, coefficient := (-14053762653020064155959296) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 12736222404299433141338112, coefficient := (-12736222404299433141338112) }, { argument := 131314844789156224457244672, coefficient := (-131314844789156224457244672) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 12736222404299433141338112, coefficient := (-12736222404299433141338112) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 677215687842404341515288576, coefficient := (-677215687842404341515288576) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 131314844789156224457244672, coefficient := (-131314844789156224457244672) }, { argument := 677215687842404341515288576, coefficient := (-677215687842404341515288576) }, { argument := 14053762653020064155959296, coefficient := (-14053762653020064155959296) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 15810482984647572175454208, coefficient := (-15810482984647572175454208) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 8492600576414271160394448896, coefficient := (-8492600576414271160394448896) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 30664943410676024734553997312, coefficient := (-30664943410676024734553997312) }, { argument := 337006961683509361030201344, coefficient := (-337006961683509361030201344) }, { argument := 8492597758674113901260439552, coefficient := (-8492597758674113901260439552) }, { argument := 337545311462556500584562688, coefficient := (-337545311462556500584562688) }, { argument := 302552575824492429551075328, coefficient := (-302552575824492429551075328) }, { argument := 409145832075826061314621440, coefficient := (-409145832075826061314621440) }, { argument := 16688843150461326185201664, coefficient := (-16688843150461326185201664) }, { argument := 160040792483561687371671928832, coefficient := (-160040792483561687371671928832) }, { argument := 160040551316401746331958247424, coefficient := (-160040551316401746331958247424) }, { argument := 160543410185339695405849378816, coefficient := (-160543410185339695405849378816) }, { argument := 18674095478173061267124960362496, coefficient := (-18674095478173061267124960362496) }, { argument := 245195587980667183939492773888, coefficient := (-245195587980667183939492773888) }, { argument := 195030014314717396792376295424000, coefficient := (-195030014314717396792376295424000) }, { argument := 243707884180182901928318992384, coefficient := (-243707884180182901928318992384) }, { argument := 8104500907894536918341255168, coefficient := (-8104500907894536918341255168) }, { argument := 245195587980667183939492773888, coefficient := (-245195587980667183939492773888) }, { argument := 146257098903405932281539330048, coefficient := (-146257098903405932281539330048) }, { argument := 243707884180182901928318992384, coefficient := (-243707884180182901928318992384) }, { argument := 3869669310267493535073429356544, coefficient := (-3869669310267493535073429356544) }, { argument := 159574665099938383575499407360, coefficient := (-159574665099938383575499407360) }, { argument := 18674102901731402423553679687680, coefficient := (-18674102901731402423553679687680) }, { argument := 245195587980667183939492773888, coefficient := (-245195587980667183939492773888) }, { argument := 8104500907894536918341255168, coefficient := (-8104500907894536918341255168) }, { argument := 159574665099938383575499407360, coefficient := (-159574665099938383575499407360) }, { argument := 8104500907894536918341255168, coefficient := (-8104500907894536918341255168) }, { argument := 246694655996989324116128432128, coefficient := (-246694655996989324116128432128) }, { argument := 146257098903405932281539330048, coefficient := (-146257098903405932281539330048) }, { argument := 160629620913488046974753046528, coefficient := (-160629620913488046974753046528) }, { argument := 19607478565214438084595180109824, coefficient := (-19607478565214438084595180109824) }, { argument := 31248059076088005442985263104, coefficient := (-31248059076088005442985263104) }, { argument := 712401103853107233228496931127296, coefficient := (-712401103853107233228496931127296) }, { argument := 767435893375665060879110504448, coefficient := (-767435893375665060879110504448) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13
