import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 15, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 522147808033413441171842155761631232
def positiveArguments : Array ℕ := #[
    33981, 93, 105, 45, 1185, 105,
    45, 105, 105, 4353, 27, 1185,
    4353, 93, 105, 27, 105, 15,
    435
  ]
def positiveCoefficients : Array ℕ := #[
    5384504380794432911532433952735232, 3597763239173136423925579776, 4061990753905154027012751360, 3481706360490132023153786880, 45842467079786738304858193920, 4061990753905154027012751360,
    3481706360490132023153786880, 4061990753905154027012751360, 4061990753905154027012751360, 168398530969039385519871492096, 4178047632588158427784544256, 45842467079786738304858193920,
    168398530969039385519871492096, 3597763239173136423925579776, 4061990753905154027012751360, 4178047632588158427784544256, 4061990753905154027012751360, 2321137573660088015435857920,
    33656494818071276223819939840
  ]
def positiveScales : Array ℕ := #[
    15, 6, 6, 5, 10, 6,
    5, 6, 6, 12, 4, 10,
    12, 6, 6, 4, 6, 3,
    8
  ]
def negativeArguments : Array ℕ := #[
    3251301665, 82005, 82005, 58695, 3045, 3204447185,
    3204449327, 1625735757, 945, 783, 11937009221, 5265,
    3251473697, 21087, 21087, 15093, 783, 167897933785,
    167898044455, 475, 3204447185, 3204449327, 947, 1801070193,
    3675, 3045, 13211837641, 20475, 3602142805, 82005,
    82005, 58695, 3045, 85278560725, 85278617131, 925,
    85572162005, 85572218411, 28723, 925, 71356791518959, 71356801222929,
    12770583, 611, 3
  ]
def negativeCoefficients : Array ℕ := #[
    7496991215085093486938030080, 387257663427725255749140480, 387257663427725255749140480, 277179300712033825817886720, 14379605940338069675704320, 7388952139926750647937925120,
    7388957079042476383670370304, 7497382860214365423642083328, 285608724883956142524334080, 14790451824347728809295872, 27524869263162252664495931392, 397812152516938912801751040,
    7497387893869654537135980544, 398322168097088834484830208, 398322168097088834484830208, 285098709303806220841254912, 14790451824347728809295872, 193573138439782966034075484160,
    193573266033605880873830318080, 18375672458142363455533875200, 7388952139926750647937925120, 7388957079042476383670370304, 18317644018800861255147978752, 8305970227264417088743145472,
    277675149192735138565324800, 14379605940338069675704320, 30464423463366191567687647232, 386761814947023943001702400, 8305975805098656376668815360, 387257663427725255749140480,
    387257663427725255749140480, 277179300712033825817886720, 14379605940338069675704320, 196638973083546734187197235200, 196639103146927511894818291712, 17892102130296511785651404800,
    197315971542530926525032693760, 197316101605911704232653750272, 555583621068655900561367891968, 17892102130296511785651404800, 80340604923784480414725308416, 80340615849483399418343325696,
    60307373125904882382057504768, 23636917625105229623855153152, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    31, 16, 16, 15, 11, 31,
    31, 30, 9, 9, 33, 12,
    31, 14, 14, 13, 9, 37,
    37, 8, 31, 31, 9, 30,
    11, 11, 33, 14, 31, 16,
    16, 15, 11, 36, 36, 9,
    36, 36, 14, 9, 46, 46,
    23, 9, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    15052440688628755, 6539158811107971, 6714245517659862, 5491853096329661, 10210671343785621, 6714245517659862,
    5491853096329661, 6714245517659862, 6714245517659862, 12087794304787900, 4754887502147955, 10210671343785621,
    12087794304787900, 6539158811107971, 6714245517659862, 4754887502147955, 6714245517659862, 3906890595303263,
    8764871590716857
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    31598370273572334, 16323424255808103, 16323424255808103, 15840949991965165, 11572226512796267, 31577428345856933,
    31577429310220384, 30598445638436938, 9884170522387776, 9612868497299083, 33474722368180485, 12362217815913081,
    31598446607045214, 14364066240305450, 14364066240305450, 13881591978134763, 9612868497299083, 37288793519798431,
    37288794470751215, 8891783706984896, 31577428345856933, 31577429310220384, 9887220618935413, 30746207262599884,
    11843528536141147, 11572226512796267, 33621112094588297, 14321575831415734, 31746208231434459, 16323424255808103,
    16323424255808103, 15840949991965165, 11572226512796267, 36311464038325929, 36311464992570804, 9853309557248504,
    36316422490018098, 36316423440988925, 14809918820972644, 9853309557248504, 46020115981028361, 46020116177223680,
    23606321052376357, 9255028569818730, 1584962500724866
  ]

abbrev PositiveTerm := Fin 19
abbrev NegativeTerm := Fin 45
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
noncomputable def positiveFloor : ℝ := 487835243401 / 500000000000
noncomputable def negativeCeiling : ℝ := 793627821 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7496991215085093486938030080, coefficient := (-7496991215085093486938030080) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 277179300712033825817886720, coefficient := (-277179300712033825817886720) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 7388952139926750647937925120, coefficient := (-7388952139926750647937925120) }, { argument := 7388957079042476383670370304, coefficient := (-7388957079042476383670370304) }, { argument := 7497382860214365423642083328, coefficient := (-7497382860214365423642083328) }, { argument := 285608724883956142524334080, coefficient := (-285608724883956142524334080) }, { argument := 14790451824347728809295872, coefficient := (-14790451824347728809295872) }, { argument := 27524869263162252664495931392, coefficient := (-27524869263162252664495931392) }, { argument := 397812152516938912801751040, coefficient := (-397812152516938912801751040) }, { argument := 7497387893869654537135980544, coefficient := (-7497387893869654537135980544) }, { argument := 398322168097088834484830208, coefficient := (-398322168097088834484830208) }, { argument := 398322168097088834484830208, coefficient := (-398322168097088834484830208) }, { argument := 285098709303806220841254912, coefficient := (-285098709303806220841254912) }, { argument := 14790451824347728809295872, coefficient := (-14790451824347728809295872) }, { argument := 193573138439782966034075484160, coefficient := (-193573138439782966034075484160) }, { argument := 193573266033605880873830318080, coefficient := (-193573266033605880873830318080) }, { argument := 18375672458142363455533875200, coefficient := (-18375672458142363455533875200) }, { argument := 7388952139926750647937925120, coefficient := (-7388952139926750647937925120) }, { argument := 7388957079042476383670370304, coefficient := (-7388957079042476383670370304) }, { argument := 18317644018800861255147978752, coefficient := (-18317644018800861255147978752) }, { argument := 8305970227264417088743145472, coefficient := (-8305970227264417088743145472) }, { argument := 277675149192735138565324800, coefficient := (-277675149192735138565324800) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 30464423463366191567687647232, coefficient := (-30464423463366191567687647232) }, { argument := 386761814947023943001702400, coefficient := (-386761814947023943001702400) }, { argument := 8305975805098656376668815360, coefficient := (-8305975805098656376668815360) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 387257663427725255749140480, coefficient := (-387257663427725255749140480) }, { argument := 277179300712033825817886720, coefficient := (-277179300712033825817886720) }, { argument := 14379605940338069675704320, coefficient := (-14379605940338069675704320) }, { argument := 196638973083546734187197235200, coefficient := (-196638973083546734187197235200) }, { argument := 196639103146927511894818291712, coefficient := (-196639103146927511894818291712) }, { argument := 17892102130296511785651404800, coefficient := (-17892102130296511785651404800) }, { argument := 197315971542530926525032693760, coefficient := (-197315971542530926525032693760) }, { argument := 197316101605911704232653750272, coefficient := (-197316101605911704232653750272) }, { argument := 555583621068655900561367891968, coefficient := (-555583621068655900561367891968) }, { argument := 17892102130296511785651404800, coefficient := (-17892102130296511785651404800) }, { argument := 80340604923784480414725308416, coefficient := (-80340604923784480414725308416) }, { argument := 80340615849483399418343325696, coefficient := (-80340615849483399418343325696) }, { argument := 60307373125904882382057504768, coefficient := (-60307373125904882382057504768) }, { argument := 23636917625105229623855153152, coefficient := (-23636917625105229623855153152) }, { argument := 5384504380794432911532433952735232, coefficient := 5384504380794432911532433952735232 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 45842467079786738304858193920, coefficient := 45842467079786738304858193920 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 3481706360490132023153786880, coefficient := 3481706360490132023153786880 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 168398530969039385519871492096, coefficient := 168398530969039385519871492096 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 45842467079786738304858193920, coefficient := 45842467079786738304858193920 }, { argument := 168398530969039385519871492096, coefficient := 168398530969039385519871492096 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 2321137573660088015435857920, coefficient := 2321137573660088015435857920 }, { argument := 33656494818071276223819939840, coefficient := 33656494818071276223819939840 }] }

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


end Parent2

namespace Parent2

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 1287893821292512444101323181260800
def positiveArguments : Array ℕ := #[
    385, 25, 15, 25, 765, 25,
    15, 12255, 785, 435, 765, 25,
    785, 25, 765, 25, 15, 141,
    105, 111, 9, 1929, 3489, 105,
    1929, 57, 57, 111, 111, 3489,
    111, 141, 9, 129, 387, 817,
    2107, 1763, 49321, 1505, 1763, 1591,
    817, 817, 1591, 49321, 1591, 129,
    2107, 87, 1305, 2291, 87, 725,
    87, 2291, 4553, 725, 70267, 4495,
    1305
  ]
def positiveCoefficients : Array ℕ := #[
    59575864390608925729520353280, 1934281311383406679529881600, 37138201178561408246973726720, 1934281311383406679529881600, 59189008128332244393614376960, 61897001964269013744956211200,
    37138201178561408246973726720, 948184698840145954305547960320, 60736433177438969737238282240, 33656494818071276223819939840, 59189008128332244393614376960, 1934281311383406679529881600,
    60736433177438969737238282240, 1934281311383406679529881600, 59189008128332244393614376960, 61897001964269013744956211200, 2321137573660088015435857920, 5454673298101206836274266112,
    4061990753905154027012751360, 4294104511271162828556337152, 5570730176784211237046059008, 74624572993171829696262832128, 134974149908334118097595138048, 4061990753905154027012751360,
    74624572993171829696262832128, 4410161389954167229328130048, 4410161389954167229328130048, 4294104511271162828556337152, 4294104511271162828556337152, 134974149908334118097595138048,
    4294104511271162828556337152, 5454673298101206836274266112, 5570730176784211237046059008, 39923566266953513865496756224, 29942674700215135399122567168, 31606156628004865143518265344,
    40755307230848378737694605312, 545622072315031356161789001728, 954006885587410008410932903936, 29110933736320270526924718080, 545622072315031356161789001728, 30774415664110000271320416256,
    31606156628004865143518265344, 31606156628004865143518265344, 30774415664110000271320416256, 954006885587410008410932903936, 30774415664110000271320416256, 39923566266953513865496756224,
    40755307230848378737694605312, 26925195854457020979055951872, 403877937816855314685839278080, 709030157500701552448473399296, 26925195854457020979055951872, 448753264240950349650932531200,
    26925195854457020979055951872, 709030157500701552448473399296, 704542624858292048951964073984, 448753264240950349650932531200, 10873291592558226972042095230976, 695567559573473041958945423360,
    403877937816855314685839278080
  ]
def positiveScales : Array ℕ := #[
    8, 4, 3, 4, 9, 4,
    3, 13, 9, 8, 9, 4,
    9, 4, 9, 4, 3, 7,
    6, 6, 3, 10, 11, 6,
    10, 5, 5, 6, 6, 11,
    6, 7, 3, 7, 8, 9,
    11, 10, 15, 10, 10, 10,
    9, 9, 10, 15, 10, 7,
    11, 6, 10, 11, 6, 9,
    6, 11, 12, 9, 16, 12,
    10
  ]
def negativeArguments : Array ℕ := #[
    5, 3, 43
  ]
def negativeCoefficients : Array ℕ := #[
    1584563250285286751870879006720, 475368975085586025561263702016, 3406810988113366516522389864448
  ]
def negativeScales : Array ℕ := #[
    2, 1, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8588714635582006, 4643856189773592, 3906890595303263, 4643856189773592, 9579315937579817, 4643856189773592,
    3906890595303263, 13581082863753994, 9616548843778436, 8764871590716857, 9579315937579817, 4643856189773592,
    9616548843778436, 4643856189773592, 9579315937579817, 4643856189773592, 3906890595303263, 7139551352398793,
    6714245517659862, 6794415866314396, 3169925001442312, 10913637427705176, 11768597882173550, 6714245517659862,
    10913637427705176, 5832890014087662, 5832890014087662, 6794415866314396, 6794415866314396, 11768597882173550,
    6794415866314396, 7139551352398793, 3169925001442312, 7011227255423254, 8596189756144093, 9674192268143262,
    11040974598817306, 10783816759291497, 15589914430717656, 10555547771646966, 10783816759291497, 10635718120330130,
    9674192268143262, 9674192268143262, 10635718120330130, 15589914430717656, 10635718120330130, 7011227255423254,
    11040974598817306, 6442943495848725, 10349834091457246, 11161761743304674, 6442943495848725, 9501837184902278,
    6442943495848725, 11161761743304674, 12152601744019198, 9501837184902278, 16100559684578918, 12134105400401809,
    10349834091457246
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    2321928094887363, 1584962500724866, 5426264754702117
  ]

abbrev PositiveTerm := Fin 61
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
noncomputable def positiveFloor : ℝ := 220689687 / 62500000000
noncomputable def negativeCeiling : ℝ := 137938367 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 59575864390608925729520353280, coefficient := 59575864390608925729520353280 }, { argument := 1934281311383406679529881600, coefficient := 1934281311383406679529881600 }, { argument := 37138201178561408246973726720, coefficient := 37138201178561408246973726720 }, { argument := 1934281311383406679529881600, coefficient := 1934281311383406679529881600 }, { argument := 59189008128332244393614376960, coefficient := 59189008128332244393614376960 }, { argument := 61897001964269013744956211200, coefficient := 61897001964269013744956211200 }, { argument := 37138201178561408246973726720, coefficient := 37138201178561408246973726720 }, { argument := 948184698840145954305547960320, coefficient := 948184698840145954305547960320 }, { argument := 60736433177438969737238282240, coefficient := 60736433177438969737238282240 }, { argument := 33656494818071276223819939840, coefficient := 33656494818071276223819939840 }, { argument := 59189008128332244393614376960, coefficient := 59189008128332244393614376960 }, { argument := 1934281311383406679529881600, coefficient := 1934281311383406679529881600 }, { argument := 60736433177438969737238282240, coefficient := 60736433177438969737238282240 }, { argument := 1934281311383406679529881600, coefficient := 1934281311383406679529881600 }, { argument := 59189008128332244393614376960, coefficient := 59189008128332244393614376960 }, { argument := 61897001964269013744956211200, coefficient := 61897001964269013744956211200 }, { argument := 2321137573660088015435857920, coefficient := 2321137573660088015435857920 }, { argument := 1584563250285286751870879006720, coefficient := (-1584563250285286751870879006720) }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 39923566266953513865496756224, coefficient := 39923566266953513865496756224 }, { argument := 29942674700215135399122567168, coefficient := 29942674700215135399122567168 }, { argument := 31606156628004865143518265344, coefficient := 31606156628004865143518265344 }, { argument := 40755307230848378737694605312, coefficient := 40755307230848378737694605312 }, { argument := 545622072315031356161789001728, coefficient := 545622072315031356161789001728 }, { argument := 954006885587410008410932903936, coefficient := 954006885587410008410932903936 }, { argument := 29110933736320270526924718080, coefficient := 29110933736320270526924718080 }, { argument := 545622072315031356161789001728, coefficient := 545622072315031356161789001728 }, { argument := 30774415664110000271320416256, coefficient := 30774415664110000271320416256 }, { argument := 31606156628004865143518265344, coefficient := 31606156628004865143518265344 }, { argument := 31606156628004865143518265344, coefficient := 31606156628004865143518265344 }, { argument := 30774415664110000271320416256, coefficient := 30774415664110000271320416256 }, { argument := 954006885587410008410932903936, coefficient := 954006885587410008410932903936 }, { argument := 30774415664110000271320416256, coefficient := 30774415664110000271320416256 }, { argument := 39923566266953513865496756224, coefficient := 39923566266953513865496756224 }, { argument := 40755307230848378737694605312, coefficient := 40755307230848378737694605312 }, { argument := 3406810988113366516522389864448, coefficient := (-3406810988113366516522389864448) }, { argument := 26925195854457020979055951872, coefficient := 26925195854457020979055951872 }, { argument := 403877937816855314685839278080, coefficient := 403877937816855314685839278080 }, { argument := 709030157500701552448473399296, coefficient := 709030157500701552448473399296 }, { argument := 26925195854457020979055951872, coefficient := 26925195854457020979055951872 }, { argument := 448753264240950349650932531200, coefficient := 448753264240950349650932531200 }, { argument := 26925195854457020979055951872, coefficient := 26925195854457020979055951872 }, { argument := 709030157500701552448473399296, coefficient := 709030157500701552448473399296 }, { argument := 704542624858292048951964073984, coefficient := 704542624858292048951964073984 }, { argument := 448753264240950349650932531200, coefficient := 448753264240950349650932531200 }, { argument := 10873291592558226972042095230976, coefficient := 10873291592558226972042095230976 }, { argument := 695567559573473041958945423360, coefficient := 695567559573473041958945423360 }, { argument := 403877937816855314685839278080, coefficient := 403877937816855314685839278080 }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15
