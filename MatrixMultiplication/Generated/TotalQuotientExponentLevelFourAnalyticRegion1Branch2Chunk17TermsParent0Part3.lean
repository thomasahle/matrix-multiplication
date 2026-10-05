import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 17, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent0

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1685735875193947148492705976287232)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4270986225, 409772115, 5548905, 1744429365, 65542692555, 131075470845,
    3498772995, 10098087129, 18364459815, 10098087129, 271355679, 10195529953,
    20389517687, 544253577, 10098087129, 18364459815, 10098087129, 217,
    217, 11714355, 865074465, 9016526475, 865074465, 11714355,
    3527623827, 132541889389, 265063729931, 7075296501, 10098087129, 18364459815,
    10098087129, 3527623827, 132541889389, 265063729931, 7075296501, 10098087129,
    18364459815, 10098087129, 4501, 4501, 10098087129, 18364459815,
    10098087129, 2261, 2261, 819942170403, 11714355, 29130574022877,
    184346955, 5548905, 233033741228043, 5548905, 5548905, 475356195,
    5548905, 184346955, 475356195, 6570388318197, 5548905, 5548905,
    11714355, 57013837999975, 92517369, 5197605
  ]
def negativeCoefficients : Array ℕ := #[
    315143159339655518411449958400, 30235845335790715445559951360, 204718460848654599019560960, 64358084101637332639867207680, 2418098550927826799868782837760, 2417915665018692863841030635520,
    64540970010771268667619409920, 46569207225670862614472687616, 169382245129614229316850155520, 46569207225670862614472687616, 2502814381730340713772613632, 94037165869415486661563777024,
    94030053639615833593817858048, 2509926611529993781518532608, 46569207225670862614472687616, 169382245129614229316850155520, 46569207225670862614472687616, 2098695222850996247289921536,
    2098695222850996247289921536, 216091708673579854520647680, 31915614521112421859202170880, 332651112636303047212086067200, 31915614521112421859202170880, 216091708673579854520647680,
    65073173924988858558087954432, 2444966312604802653200658202624, 2444781394630011673439264309248, 65258091899779838319481847808, 46569207225670862614472687616, 169382245129614229316850155520,
    46569207225670862614472687616, 65073173924988858558087954432, 2444966312604802653200658202624, 2444781394630011673439264309248, 65258091899779838319481847808, 1490214631221467603663126003712,
    5420231844147655338139204976640, 1490214631221467603663126003712, 43531000912683567322819985408, 43531000912683567322819985408, 46569207225670862614472687616, 169382245129614229316850155520,
    46569207225670862614472687616, 43734100450378825024170622976, 43734100450378825024170622976, 3692691253092306534046629888, 216091708673579854520647680, 131192442314517507820058836992,
    1700300549826325697412464640, 204718460848654599019560960, 131186333769920880716248252416, 204718460848654599019560960, 204718460848654599019560960, 8768774073017371991337861120,
    204718460848654599019560960, 1700300549826325697412464640, 8768774073017371991337861120, 3698799797688933637857214464, 204718460848654599019560960, 204718460848654599019560960,
    216091708673579854520647680, 64191874892912308733240934400, 426661057078987446420504576, 23969722307808283506769920
  ]
def negativeScales : Array ℕ := #[
    31, 28, 22, 30, 35, 36,
    31, 33, 34, 33, 28, 33,
    34, 29, 33, 34, 33, 7,
    7, 23, 29, 33, 29, 23,
    31, 36, 37, 32, 33, 34,
    33, 31, 36, 37, 32, 33,
    34, 33, 12, 12, 33, 34,
    33, 11, 11, 39, 23, 44,
    27, 22, 47, 22, 22, 28,
    22, 27, 28, 42, 22, 22,
    23, 45, 26, 22
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31991922119724051, 28610246571371618, 22403771672871506, 30700108035525006, 35931715897860371, 36931606779641439,
    31704201917725985, 33233362979388147, 34096197409131470, 33233362979388147, 28015609861180364, 33247217715958799,
    34247108597754219, 29019703743374031, 33233362979388147, 34096197409131470, 33233362979388147, 7761551232733342,
    7761551232733342, 23481774184872917, 29688249083420169, 33069924610922346, 29688249083420169, 23481774184872917,
    31716049579426571, 36947657444119108, 37947548325896033, 32720143461630567, 33233362979388147, 34096197409131470,
    33233362979388147, 31716049579426571, 36947657444119108, 37947548325896033, 32720143461630567, 33233362979388147,
    34096197409131470, 33233362979388147, 12136029849385552, 12136029849385552, 33233362979388147, 34096197409131470,
    33233362979388147, 11142745276751530, 11142745276751530, 39576731205427726, 23481774184872917, 44727599363980043,
    27457848345627353, 22403771672871506, 47727532188066222, 22403771672871506, 22403771672871506, 28824433722398829,
    22403771672871506, 27457848345627353, 28824433722398829, 42579115776806669, 22403771672871506, 22403771672871506,
    23481774184872917, 45696377356230089, 26463220903546899, 22309415567467788
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
noncomputable def negativeCeiling : ℝ := 444210733 / 40000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 315143159339655518411449958400, coefficient := (-315143159339655518411449958400) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 64358084101637332639867207680, coefficient := (-64358084101637332639867207680) }, { argument := 2418098550927826799868782837760, coefficient := (-2418098550927826799868782837760) }, { argument := 2417915665018692863841030635520, coefficient := (-2417915665018692863841030635520) }, { argument := 64540970010771268667619409920, coefficient := (-64540970010771268667619409920) }, { argument := 46569207225670862614472687616, coefficient := (-46569207225670862614472687616) }, { argument := 169382245129614229316850155520, coefficient := (-169382245129614229316850155520) }, { argument := 46569207225670862614472687616, coefficient := (-46569207225670862614472687616) }, { argument := 2502814381730340713772613632, coefficient := (-2502814381730340713772613632) }, { argument := 94037165869415486661563777024, coefficient := (-94037165869415486661563777024) }, { argument := 94030053639615833593817858048, coefficient := (-94030053639615833593817858048) }, { argument := 2509926611529993781518532608, coefficient := (-2509926611529993781518532608) }, { argument := 46569207225670862614472687616, coefficient := (-46569207225670862614472687616) }, { argument := 169382245129614229316850155520, coefficient := (-169382245129614229316850155520) }, { argument := 46569207225670862614472687616, coefficient := (-46569207225670862614472687616) }, { argument := 2098695222850996247289921536, coefficient := (-2098695222850996247289921536) }, { argument := 2098695222850996247289921536, coefficient := (-2098695222850996247289921536) }, { argument := 216091708673579854520647680, coefficient := (-216091708673579854520647680) }, { argument := 31915614521112421859202170880, coefficient := (-31915614521112421859202170880) }, { argument := 332651112636303047212086067200, coefficient := (-332651112636303047212086067200) }, { argument := 31915614521112421859202170880, coefficient := (-31915614521112421859202170880) }, { argument := 216091708673579854520647680, coefficient := (-216091708673579854520647680) }, { argument := 65073173924988858558087954432, coefficient := (-65073173924988858558087954432) }, { argument := 2444966312604802653200658202624, coefficient := (-2444966312604802653200658202624) }, { argument := 2444781394630011673439264309248, coefficient := (-2444781394630011673439264309248) }, { argument := 65258091899779838319481847808, coefficient := (-65258091899779838319481847808) }, { argument := 46569207225670862614472687616, coefficient := (-46569207225670862614472687616) }, { argument := 169382245129614229316850155520, coefficient := (-169382245129614229316850155520) }, { argument := 46569207225670862614472687616, coefficient := (-46569207225670862614472687616) }, { argument := 65073173924988858558087954432, coefficient := (-65073173924988858558087954432) }, { argument := 2444966312604802653200658202624, coefficient := (-2444966312604802653200658202624) }, { argument := 2444781394630011673439264309248, coefficient := (-2444781394630011673439264309248) }, { argument := 65258091899779838319481847808, coefficient := (-65258091899779838319481847808) }, { argument := 1490214631221467603663126003712, coefficient := (-1490214631221467603663126003712) }, { argument := 5420231844147655338139204976640, coefficient := (-5420231844147655338139204976640) }, { argument := 1490214631221467603663126003712, coefficient := (-1490214631221467603663126003712) }, { argument := 43531000912683567322819985408, coefficient := (-43531000912683567322819985408) }, { argument := 43531000912683567322819985408, coefficient := (-43531000912683567322819985408) }, { argument := 46569207225670862614472687616, coefficient := (-46569207225670862614472687616) }, { argument := 169382245129614229316850155520, coefficient := (-169382245129614229316850155520) }, { argument := 46569207225670862614472687616, coefficient := (-46569207225670862614472687616) }, { argument := 43734100450378825024170622976, coefficient := (-43734100450378825024170622976) }, { argument := 43734100450378825024170622976, coefficient := (-43734100450378825024170622976) }, { argument := 3692691253092306534046629888, coefficient := (-3692691253092306534046629888) }, { argument := 216091708673579854520647680, coefficient := (-216091708673579854520647680) }, { argument := 131192442314517507820058836992, coefficient := (-131192442314517507820058836992) }, { argument := 1700300549826325697412464640, coefficient := (-1700300549826325697412464640) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 131186333769920880716248252416, coefficient := (-131186333769920880716248252416) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 8768774073017371991337861120, coefficient := (-8768774073017371991337861120) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 1700300549826325697412464640, coefficient := (-1700300549826325697412464640) }, { argument := 8768774073017371991337861120, coefficient := (-8768774073017371991337861120) }, { argument := 3698799797688933637857214464, coefficient := (-3698799797688933637857214464) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 216091708673579854520647680, coefficient := (-216091708673579854520647680) }, { argument := 64191874892912308733240934400, coefficient := (-64191874892912308733240934400) }, { argument := 426661057078987446420504576, coefficient := (-426661057078987446420504576) }, { argument := 23969722307808283506769920, coefficient := (-23969722307808283506769920) }] }

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

end TermShard6


end Parent0

namespace Parent0

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 99167314184971720806719411265208320
def positiveArguments : Array ℕ := #[
    155, 217, 2597, 3885, 1127, 217,
    4501, 2261, 217, 2597, 217, 31005,
    24115, 3445, 32383, 382395, 26871, 24115,
    382395, 3445, 26871, 26871, 26871, 26871,
    26871, 31005, 32383, 7145, 30009, 130039,
    4287, 4287, 10003, 130039, 130039, 4287,
    1604767, 64305, 30009, 130039, 10003, 64305,
    10003, 130039, 130039, 4287
  ]
def positiveCoefficients : Array ℕ := #[
    785943372141502228927955987333120, 8394780891403984989159686144, 200933142626508285869564100608, 150293657894490698999471800320, 174394803034327946226414125056, 8394780891403984989159686144,
    174124003650734269291279941632, 174936401801515300096682491904, 8394780891403984989159686144, 200933142626508285869564100608, 8394780891403984989159686144, 599723920594425240988239790080,
    466451938240108520768630947840, 533087929417266880878435368960, 626378317065288585032161558528, 7396595020664577972188290744320, 16632343397818726683407183511552, 466451938240108520768630947840,
    7396595020664577972188290744320, 533087929417266880878435368960, 519760731181835208856474484736, 519760731181835208856474484736, 519760731181835208856474484736, 16632343397818726683407183511552,
    519760731181835208856474484736, 599723920594425240988239790080, 626378317065288585032161558528, 276408799396688814504820080640, 4643667829864372083680977354752, 10061280298039472847975450935296,
    331690559276026577405784096768, 5307048948416425238492545548288, 386972319155364340306748112896, 10061280298039472847975450935296, 10061280298039472847975450935296, 5307048948416425238492545548288,
    124162832688992615475565180223488, 9950716778280797322173522903040, 4643667829864372083680977354752, 10061280298039472847975450935296, 386972319155364340306748112896, 9950716778280797322173522903040,
    386972319155364340306748112896, 10061280298039472847975450935296, 10061280298039472847975450935296, 331690559276026577405784096768
  ]
def positiveScales : Array ℕ := #[
    7, 7, 11, 11, 10, 7,
    12, 11, 7, 11, 7, 14,
    14, 11, 14, 18, 14, 14,
    18, 11, 14, 14, 14, 14,
    14, 14, 14, 12, 14, 16,
    12, 12, 13, 16, 16, 12,
    20, 15, 14, 16, 13, 15,
    13, 16, 16, 12
  ]
def negativeArguments : Array ℕ := #[
    207077244636125, 281017177, 14253458729775, 281017177, 281017177, 92517369,
    5197605, 2324491, 2324491, 12169489617, 22131528495, 12169489617,
    2597, 2597, 217, 217, 7, 689
  ]
def negativeCoefficients : Array ℕ := #[
    233148250445040397888520192000, 647981493054417264133013504, 64191871424155433239471718400, 647981493054417264133013504, 647981493054417264133013504, 426661057078987446420504576,
    23969722307808283506769920, 5488549194066072236214714368, 5488549194066072236214714368, 56121865118116167766159392768, 204127321053637660971588648960, 56121865118116167766159392768,
    50233285656627071467391025152, 50233285656627071467391025152, 2098695222850996247289921536, 2098695222850996247289921536, 1109194275199700726309615304704, 54588203972328128601951781781504
  ]
def negativeScales : Array ℕ := #[
    47, 28, 43, 28, 28, 26,
    22, 21, 21, 33, 34, 33,
    11, 11, 7, 7, 2, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    7276124405274237, 7761551232426566, 11342630298678407, 11923698882884927, 10138271800172220, 7761551232426566,
    12136029849385551, 11142745276751528, 7761551232426566, 11342630298678407, 7761551232426566, 14920213268647998,
    14557643189649153, 11750288267577617, 14982949023272186, 18544704133941688, 14713762391560349, 14557643189649153,
    18544704133941688, 11750288267577617, 14713762391560349, 14713762391560349, 14713762391560349, 14713762391560349,
    14713762391560349, 14920213268647998, 14982949023272186, 12802718295940877, 14873107623709114, 16988584840078851,
    12065752701816972, 12065752701816972, 13288145123153420, 16988584840078851, 16988584840078851, 12065752701816972,
    20613932413495902, 15972643296487579, 14873107623709114, 16988584840078851, 13288145123153420, 15972643296487579,
    13288145123153420, 16988584840078851, 16988584840078851, 12065752701816972
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    47557162355405098, 28066083076076542, 43696377278270714, 28066083076076542, 28066083076076542, 26463220903546899,
    22309415567467788, 21148483409343020, 21148483409343020, 33502549612203830, 34365384041946861, 33502549612203830,
    11342630298678409, 11342630298678409, 7761551232733342, 7761551232733342, 2807354922807594, 9428360172704312
  ]

abbrev PositiveTerm := Fin 46
abbrev NegativeTerm := Fin 18
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
noncomputable def positiveFloor : ℝ := 129811346601 / 1000000000000
noncomputable def negativeCeiling : ℝ := 6547319259 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 233148250445040397888520192000, coefficient := (-233148250445040397888520192000) }, { argument := 647981493054417264133013504, coefficient := (-647981493054417264133013504) }, { argument := 64191871424155433239471718400, coefficient := (-64191871424155433239471718400) }, { argument := 647981493054417264133013504, coefficient := (-647981493054417264133013504) }, { argument := 647981493054417264133013504, coefficient := (-647981493054417264133013504) }, { argument := 426661057078987446420504576, coefficient := (-426661057078987446420504576) }, { argument := 23969722307808283506769920, coefficient := (-23969722307808283506769920) }, { argument := 5488549194066072236214714368, coefficient := (-5488549194066072236214714368) }, { argument := 5488549194066072236214714368, coefficient := (-5488549194066072236214714368) }, { argument := 56121865118116167766159392768, coefficient := (-56121865118116167766159392768) }, { argument := 204127321053637660971588648960, coefficient := (-204127321053637660971588648960) }, { argument := 56121865118116167766159392768, coefficient := (-56121865118116167766159392768) }, { argument := 50233285656627071467391025152, coefficient := (-50233285656627071467391025152) }, { argument := 50233285656627071467391025152, coefficient := (-50233285656627071467391025152) }, { argument := 2098695222850996247289921536, coefficient := (-2098695222850996247289921536) }, { argument := 2098695222850996247289921536, coefficient := (-2098695222850996247289921536) }, { argument := 785943372141502228927955987333120, coefficient := 785943372141502228927955987333120 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 200933142626508285869564100608, coefficient := 200933142626508285869564100608 }, { argument := 150293657894490698999471800320, coefficient := 150293657894490698999471800320 }, { argument := 174394803034327946226414125056, coefficient := 174394803034327946226414125056 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 174124003650734269291279941632, coefficient := 174124003650734269291279941632 }, { argument := 174936401801515300096682491904, coefficient := 174936401801515300096682491904 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 200933142626508285869564100608, coefficient := 200933142626508285869564100608 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 599723920594425240988239790080, coefficient := 599723920594425240988239790080 }, { argument := 466451938240108520768630947840, coefficient := 466451938240108520768630947840 }, { argument := 533087929417266880878435368960, coefficient := 533087929417266880878435368960 }, { argument := 626378317065288585032161558528, coefficient := 626378317065288585032161558528 }, { argument := 7396595020664577972188290744320, coefficient := 7396595020664577972188290744320 }, { argument := 16632343397818726683407183511552, coefficient := 16632343397818726683407183511552 }, { argument := 466451938240108520768630947840, coefficient := 466451938240108520768630947840 }, { argument := 7396595020664577972188290744320, coefficient := 7396595020664577972188290744320 }, { argument := 533087929417266880878435368960, coefficient := 533087929417266880878435368960 }, { argument := 519760731181835208856474484736, coefficient := 519760731181835208856474484736 }, { argument := 519760731181835208856474484736, coefficient := 519760731181835208856474484736 }, { argument := 519760731181835208856474484736, coefficient := 519760731181835208856474484736 }, { argument := 16632343397818726683407183511552, coefficient := 16632343397818726683407183511552 }, { argument := 519760731181835208856474484736, coefficient := 519760731181835208856474484736 }, { argument := 599723920594425240988239790080, coefficient := 599723920594425240988239790080 }, { argument := 626378317065288585032161558528, coefficient := 626378317065288585032161558528 }, { argument := 54588203972328128601951781781504, coefficient := (-54588203972328128601951781781504) }, { argument := 276408799396688814504820080640, coefficient := 276408799396688814504820080640 }, { argument := 4643667829864372083680977354752, coefficient := 4643667829864372083680977354752 }, { argument := 10061280298039472847975450935296, coefficient := 10061280298039472847975450935296 }, { argument := 331690559276026577405784096768, coefficient := 331690559276026577405784096768 }, { argument := 5307048948416425238492545548288, coefficient := 5307048948416425238492545548288 }, { argument := 386972319155364340306748112896, coefficient := 386972319155364340306748112896 }, { argument := 10061280298039472847975450935296, coefficient := 10061280298039472847975450935296 }, { argument := 10061280298039472847975450935296, coefficient := 10061280298039472847975450935296 }, { argument := 5307048948416425238492545548288, coefficient := 5307048948416425238492545548288 }, { argument := 124162832688992615475565180223488, coefficient := 124162832688992615475565180223488 }, { argument := 9950716778280797322173522903040, coefficient := 9950716778280797322173522903040 }, { argument := 4643667829864372083680977354752, coefficient := 4643667829864372083680977354752 }, { argument := 10061280298039472847975450935296, coefficient := 10061280298039472847975450935296 }, { argument := 386972319155364340306748112896, coefficient := 386972319155364340306748112896 }, { argument := 9950716778280797322173522903040, coefficient := 9950716778280797322173522903040 }, { argument := 386972319155364340306748112896, coefficient := 386972319155364340306748112896 }, { argument := 10061280298039472847975450935296, coefficient := 10061280298039472847975450935296 }, { argument := 10061280298039472847975450935296, coefficient := 10061280298039472847975450935296 }, { argument := 331690559276026577405784096768, coefficient := 331690559276026577405784096768 }] }

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

end TermShard7


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17
