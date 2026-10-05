import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 2,
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

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-733545398637307265904104699854848)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3526975833, 33189, 31395, 42159, 28020699, 4473425943,
    178552255077, 4473425943, 112070007, 20760514263, 42159, 728103792937,
    1043211, 33189, 1456097614319, 17043, 17043, 576771,
    31395, 1043211, 576771, 41631000081, 33189, 31395,
    42159, 3387482455, 744095703311, 216798873905, 756841707, 42159,
    27625205013, 1043211, 33189, 55246233891, 17043, 17043,
    576771, 31395, 1043211, 576771, 1517859549, 33189,
    31395, 42159, 18519146905, 254223186311, 74076586005, 617,
    617, 555532247657, 65959388742457, 787013793, 673491780585667, 807589317,
    25719405, 787013793, 447517647, 807589317, 12607652331, 15431643,
    32979702954905, 787013793, 25719405, 15431643
  ]
def negativeCoefficients : Array ℕ := #[
    8132652568188694901362262016, 156730621199960654997356544, 148258695729692511483985920, 199090248551301372564209664, 516890663219449159256899584, 82520143503213812445911973888,
    823426938297281487437832388608, 82520143503213812445911973888, 516831684366959491392995328, 95740973362039467410825674752, 6370887953641643922054709248, 3357786081851512808823794434048,
    157645589150749614496800571392, 5015379878398740959915409408, 3357532504710203699572598898688, 5150930685923031256129339392, 5150930685923031256129339392, 87159169238118660465556979712,
    4744278263350160367487549440, 157645589150749614496800571392, 87159169238118660465556979712, 95994550503348576662021210112, 5015379878398740959915409408, 4744278263350160367487549440,
    6370887953641643922054709248, 249952087606265331460467589120, 857883937832808127152873537536, 249952083899622694149454561280, 6980632636669235433629024256, 199090248551301372564209664,
    254797543429284573404152725504, 4926424660960925453025017856, 156730621199960654997356544, 254778284405894008144568254464, 160966583935094726754041856, 160966583935094726754041856,
    2723724038691208139548655616, 148258695729692511483985920, 4926424660960925453025017856, 2723724038691208139548655616, 6999891660059800693213495296, 156730621199960654997356544,
    148258695729692511483985920, 199090248551301372564209664, 170808981709982667339192074240, 586198756935249807171829891072, 170808977986046207459076341760, 47738062764942476850797477888,
    47738062764942476850797477888, 312736852942544912445865984, 37131834820264379244383043584, 907365126371901612352339968, 379142166510337719185759535104, 931087090460055902871355392,
    29652455110192863148769280, 907365126371901612352339968, 515952718917355818788585472, 931087090460055902871355392, 14535633495016541515526701056, 569327138115702972456370176,
    37131844484624950961603870720, 907365126371901612352339968, 29652455110192863148769280, 569327138115702972456370176
  ]
def negativeScales : Array ℕ := #[
    31, 15, 14, 15, 24, 32,
    37, 32, 26, 34, 15, 39,
    19, 15, 40, 14, 14, 19,
    14, 19, 19, 35, 15, 14,
    15, 31, 39, 37, 29, 15,
    34, 19, 15, 35, 14, 14,
    19, 14, 19, 19, 30, 15,
    14, 15, 34, 37, 36, 9,
    9, 39, 45, 29, 49, 29,
    24, 29, 28, 29, 33, 23,
    44, 29, 24, 23
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31715784544476252, 15018417540548212, 14938247200400131, 15363553026596901, 24739989609855723, 32058732986931364,
    37377555398731508, 32058732986931364, 26739824984415178, 34273123130309811, 15363553026596901, 39405353168473391,
    19992599577423370, 15018417540548212, 40405244213260111, 14056891688362847, 14056891688362847, 19137639102247209,
    14938247200400131, 19992599577423370, 19137639102247209, 35276939164920073, 15018417540548212, 14938247200400131,
    15363553026596901, 31657566328257155, 39436697232046849, 37657566306862835, 29495416352036672, 15363553026596901,
    34685266120040113, 19992599577423370, 15018417540548212, 35685157068958537, 14056891688362847, 14056891688362847,
    19137639102247209, 14938247200400131, 19992599577423370, 19137639102247209, 30499391155058937, 15018417540548212,
    14938247200400131, 15363553026596901, 34108298590437583, 37887304663927174, 36108298558984291, 9269126679149419,
    9269126679149419, 39015079703682291, 45906643267575760, 29551813679354444, 49258653667309381, 29589046585556178,
    24616353931556585, 29551813679354444, 28737369332679323, 29589046585556178, 33553580605528709, 23879388340385577,
    44906643643068233, 29551813679354444, 24616353931556585, 23879388340385577
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
noncomputable def negativeCeiling : ℝ := 5403682381 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8132652568188694901362262016, coefficient := (-8132652568188694901362262016) }, { argument := 156730621199960654997356544, coefficient := (-156730621199960654997356544) }, { argument := 148258695729692511483985920, coefficient := (-148258695729692511483985920) }, { argument := 199090248551301372564209664, coefficient := (-199090248551301372564209664) }, { argument := 516890663219449159256899584, coefficient := (-516890663219449159256899584) }, { argument := 82520143503213812445911973888, coefficient := (-82520143503213812445911973888) }, { argument := 823426938297281487437832388608, coefficient := (-823426938297281487437832388608) }, { argument := 82520143503213812445911973888, coefficient := (-82520143503213812445911973888) }, { argument := 516831684366959491392995328, coefficient := (-516831684366959491392995328) }, { argument := 95740973362039467410825674752, coefficient := (-95740973362039467410825674752) }, { argument := 6370887953641643922054709248, coefficient := (-6370887953641643922054709248) }, { argument := 3357786081851512808823794434048, coefficient := (-3357786081851512808823794434048) }, { argument := 157645589150749614496800571392, coefficient := (-157645589150749614496800571392) }, { argument := 5015379878398740959915409408, coefficient := (-5015379878398740959915409408) }, { argument := 3357532504710203699572598898688, coefficient := (-3357532504710203699572598898688) }, { argument := 5150930685923031256129339392, coefficient := (-5150930685923031256129339392) }, { argument := 5150930685923031256129339392, coefficient := (-5150930685923031256129339392) }, { argument := 87159169238118660465556979712, coefficient := (-87159169238118660465556979712) }, { argument := 4744278263350160367487549440, coefficient := (-4744278263350160367487549440) }, { argument := 157645589150749614496800571392, coefficient := (-157645589150749614496800571392) }, { argument := 87159169238118660465556979712, coefficient := (-87159169238118660465556979712) }, { argument := 95994550503348576662021210112, coefficient := (-95994550503348576662021210112) }, { argument := 5015379878398740959915409408, coefficient := (-5015379878398740959915409408) }, { argument := 4744278263350160367487549440, coefficient := (-4744278263350160367487549440) }, { argument := 6370887953641643922054709248, coefficient := (-6370887953641643922054709248) }, { argument := 249952087606265331460467589120, coefficient := (-249952087606265331460467589120) }, { argument := 857883937832808127152873537536, coefficient := (-857883937832808127152873537536) }, { argument := 249952083899622694149454561280, coefficient := (-249952083899622694149454561280) }, { argument := 6980632636669235433629024256, coefficient := (-6980632636669235433629024256) }, { argument := 199090248551301372564209664, coefficient := (-199090248551301372564209664) }, { argument := 254797543429284573404152725504, coefficient := (-254797543429284573404152725504) }, { argument := 4926424660960925453025017856, coefficient := (-4926424660960925453025017856) }, { argument := 156730621199960654997356544, coefficient := (-156730621199960654997356544) }, { argument := 254778284405894008144568254464, coefficient := (-254778284405894008144568254464) }, { argument := 160966583935094726754041856, coefficient := (-160966583935094726754041856) }, { argument := 160966583935094726754041856, coefficient := (-160966583935094726754041856) }, { argument := 2723724038691208139548655616, coefficient := (-2723724038691208139548655616) }, { argument := 148258695729692511483985920, coefficient := (-148258695729692511483985920) }, { argument := 4926424660960925453025017856, coefficient := (-4926424660960925453025017856) }, { argument := 2723724038691208139548655616, coefficient := (-2723724038691208139548655616) }, { argument := 6999891660059800693213495296, coefficient := (-6999891660059800693213495296) }, { argument := 156730621199960654997356544, coefficient := (-156730621199960654997356544) }, { argument := 148258695729692511483985920, coefficient := (-148258695729692511483985920) }, { argument := 199090248551301372564209664, coefficient := (-199090248551301372564209664) }, { argument := 170808981709982667339192074240, coefficient := (-170808981709982667339192074240) }, { argument := 586198756935249807171829891072, coefficient := (-586198756935249807171829891072) }, { argument := 170808977986046207459076341760, coefficient := (-170808977986046207459076341760) }, { argument := 47738062764942476850797477888, coefficient := (-47738062764942476850797477888) }, { argument := 47738062764942476850797477888, coefficient := (-47738062764942476850797477888) }, { argument := 312736852942544912445865984, coefficient := (-312736852942544912445865984) }, { argument := 37131834820264379244383043584, coefficient := (-37131834820264379244383043584) }, { argument := 907365126371901612352339968, coefficient := (-907365126371901612352339968) }, { argument := 379142166510337719185759535104, coefficient := (-379142166510337719185759535104) }, { argument := 931087090460055902871355392, coefficient := (-931087090460055902871355392) }, { argument := 29652455110192863148769280, coefficient := (-29652455110192863148769280) }, { argument := 907365126371901612352339968, coefficient := (-907365126371901612352339968) }, { argument := 515952718917355818788585472, coefficient := (-515952718917355818788585472) }, { argument := 931087090460055902871355392, coefficient := (-931087090460055902871355392) }, { argument := 14535633495016541515526701056, coefficient := (-14535633495016541515526701056) }, { argument := 569327138115702972456370176, coefficient := (-569327138115702972456370176) }, { argument := 37131844484624950961603870720, coefficient := (-37131844484624950961603870720) }, { argument := 907365126371901612352339968, coefficient := (-907365126371901612352339968) }, { argument := 29652455110192863148769280, coefficient := (-29652455110192863148769280) }, { argument := 569327138115702972456370176, coefficient := (-569327138115702972456370176) }] }

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

end TermShard10


end Parent1

namespace Parent1

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 110174953708074695799049879631691776
def positiveArguments : Array ℕ := #[
    7177, 1, 1, 1, 1, 155,
    1855, 2775, 805, 155, 3215, 1615,
    155, 1855
  ]
def positiveCoefficients : Array ℕ := #[
    1137241044729750301817729863122944, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 39614081257132168796771975168, 5996272065288560706542632960,
    143523673304648775621117214720, 107352612781779070713908428800, 124567716453091390161724375040, 5996272065288560706542632960, 124374288321953049493771386880, 124954572715368071497630351360,
    5996272065288560706542632960, 143523673304648775621117214720
  ]
def positiveScales : Array ℕ := #[
    12, 0, 0, 0, 0, 7,
    10, 11, 9, 7, 11, 10,
    7, 10
  ]
def negativeArguments : Array ℕ := #[
    25719405, 396078837, 447517647, 555525022313, 1068756541449, 48645,
    154641550311841, 1203705, 38295, 1237092771921687, 19665, 19665,
    665505, 36225, 1203705, 665505, 34239882883777, 38295,
    36225, 48645, 8735075690719, 14824055160289, 8735075670879, 1571713851,
    50807, 57097928901, 1257203, 39997, 114187227123, 20539,
    20539, 695083, 37835, 1257203, 695083, 3152058381,
    39997, 37835, 50807, 17487413195, 240045918439, 69949650925,
    663, 663, 828926105, 22757865227, 6631408685, 617,
    617, 1
  ]
def negativeCoefficients : Array ℕ := #[
    29652455110192863148769280, 913295617393940184982093824, 515952718917355818788585472, 312732785435476659489734656, 19253006247277985852414754816, 229719517559193891420241920,
    696443628360402937107642843136, 5684336147262606291951943680, 180843024461493063458488320, 696421318331155446254580793344, 185730673771263146254663680, 185730673771263146254663680,
    3142758506182163237940756480, 171067725841952897866137600, 5684336147262606291951943680, 3142758506182163237940756480, 19275340474573440150010855424, 180843024461493063458488320,
    171067725841952897866137600, 229719517559193891420241920, 78678567251550332729843253248, 267046437183988875011477733376, 78678567072847499515781971968, 7248250791625366806466658304,
    239929273895158064372252672, 263317720393902770373739413504, 5936973309363166571594252288, 188880492215337199612198912, 263297819403065852938835460096, 193985370383319286088204288,
    193985370383319286088204288, 3282436662012481604071456768, 178670735879373026660188160, 5936973309363166571594252288, 3282436662012481604071456768, 7268151782462284241370611712,
    188880492215337199612198912, 178670735879373026660188160, 239929273895158064372252672, 161292917859688232763585986560, 553508202922848703923699580928, 161292913582349450672183705600,
    51297140377887945141132460032, 51297140377887945141132460032, 7645493857475945761173667840, 26238032219152683101220503552, 7645493678773112547112386560, 47738062764942476850797477888,
    47738062764942476850797477888, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    24, 28, 28, 39, 39, 15,
    47, 20, 15, 50, 14, 14,
    19, 15, 20, 19, 44, 15,
    15, 15, 42, 43, 42, 30,
    15, 35, 20, 15, 36, 14,
    14, 19, 15, 20, 19, 31,
    15, 15, 15, 34, 37, 36,
    9, 9, 29, 34, 32, 9,
    9, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    12809165205323695, 0, 0, 0, 0, 7276124405274237,
    10857203471385268, 11438272056124828, 9652844973000555, 7276124405274237, 11650603022213964, 10657318449579693,
    7276124405274237, 10857203471385268
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    24616353931556585, 28561212377357150, 28737369332679323, 39015060939630717, 39959070400996633, 15570003904066736,
    47135921334457813, 20199050433859907, 15224868418015638, 50135875118105486, 14263342565830274, 14263342565830274,
    19344089979714636, 15144698069331655, 20199050433859907, 19344089979714636, 44960743013082695, 15224868418015638,
    15144698069331655, 15570003904066736, 42989957363164737, 43753005388529904, 42989957359887939, 30549691435883801,
    15632739659425936, 35732719365045167, 20261786189207869, 15287604173363601, 36732610325114775, 14326078321178237,
    14326078321178237, 19406825735062607, 15207433824679617, 20261786189207869, 19406825735062607, 31553647109974669,
    15287604173363601, 15207433824679617, 15632739659425936, 34025597844951067, 37804519450168349, 36025597806692130,
    9372865060112590, 9372865060112590, 29626668256848792, 34405646182666386, 32626668223127793, 9269126679149419,
    9269126679149419, 0
  ]

abbrev PositiveTerm := Fin 14
abbrev NegativeTerm := Fin 50
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
noncomputable def positiveFloor : ℝ := 175447004897 / 1000000000000
noncomputable def negativeCeiling : ℝ := 54027259 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 29652455110192863148769280, coefficient := (-29652455110192863148769280) }, { argument := 913295617393940184982093824, coefficient := (-913295617393940184982093824) }, { argument := 515952718917355818788585472, coefficient := (-515952718917355818788585472) }, { argument := 312732785435476659489734656, coefficient := (-312732785435476659489734656) }, { argument := 19253006247277985852414754816, coefficient := (-19253006247277985852414754816) }, { argument := 229719517559193891420241920, coefficient := (-229719517559193891420241920) }, { argument := 696443628360402937107642843136, coefficient := (-696443628360402937107642843136) }, { argument := 5684336147262606291951943680, coefficient := (-5684336147262606291951943680) }, { argument := 180843024461493063458488320, coefficient := (-180843024461493063458488320) }, { argument := 696421318331155446254580793344, coefficient := (-696421318331155446254580793344) }, { argument := 185730673771263146254663680, coefficient := (-185730673771263146254663680) }, { argument := 185730673771263146254663680, coefficient := (-185730673771263146254663680) }, { argument := 3142758506182163237940756480, coefficient := (-3142758506182163237940756480) }, { argument := 171067725841952897866137600, coefficient := (-171067725841952897866137600) }, { argument := 5684336147262606291951943680, coefficient := (-5684336147262606291951943680) }, { argument := 3142758506182163237940756480, coefficient := (-3142758506182163237940756480) }, { argument := 19275340474573440150010855424, coefficient := (-19275340474573440150010855424) }, { argument := 180843024461493063458488320, coefficient := (-180843024461493063458488320) }, { argument := 171067725841952897866137600, coefficient := (-171067725841952897866137600) }, { argument := 229719517559193891420241920, coefficient := (-229719517559193891420241920) }, { argument := 78678567251550332729843253248, coefficient := (-78678567251550332729843253248) }, { argument := 267046437183988875011477733376, coefficient := (-267046437183988875011477733376) }, { argument := 78678567072847499515781971968, coefficient := (-78678567072847499515781971968) }, { argument := 7248250791625366806466658304, coefficient := (-7248250791625366806466658304) }, { argument := 239929273895158064372252672, coefficient := (-239929273895158064372252672) }, { argument := 263317720393902770373739413504, coefficient := (-263317720393902770373739413504) }, { argument := 5936973309363166571594252288, coefficient := (-5936973309363166571594252288) }, { argument := 188880492215337199612198912, coefficient := (-188880492215337199612198912) }, { argument := 263297819403065852938835460096, coefficient := (-263297819403065852938835460096) }, { argument := 193985370383319286088204288, coefficient := (-193985370383319286088204288) }, { argument := 193985370383319286088204288, coefficient := (-193985370383319286088204288) }, { argument := 3282436662012481604071456768, coefficient := (-3282436662012481604071456768) }, { argument := 178670735879373026660188160, coefficient := (-178670735879373026660188160) }, { argument := 5936973309363166571594252288, coefficient := (-5936973309363166571594252288) }, { argument := 3282436662012481604071456768, coefficient := (-3282436662012481604071456768) }, { argument := 7268151782462284241370611712, coefficient := (-7268151782462284241370611712) }, { argument := 188880492215337199612198912, coefficient := (-188880492215337199612198912) }, { argument := 178670735879373026660188160, coefficient := (-178670735879373026660188160) }, { argument := 239929273895158064372252672, coefficient := (-239929273895158064372252672) }, { argument := 161292917859688232763585986560, coefficient := (-161292917859688232763585986560) }, { argument := 553508202922848703923699580928, coefficient := (-553508202922848703923699580928) }, { argument := 161292913582349450672183705600, coefficient := (-161292913582349450672183705600) }, { argument := 51297140377887945141132460032, coefficient := (-51297140377887945141132460032) }, { argument := 51297140377887945141132460032, coefficient := (-51297140377887945141132460032) }, { argument := 7645493857475945761173667840, coefficient := (-7645493857475945761173667840) }, { argument := 26238032219152683101220503552, coefficient := (-26238032219152683101220503552) }, { argument := 7645493678773112547112386560, coefficient := (-7645493678773112547112386560) }, { argument := 47738062764942476850797477888, coefficient := (-47738062764942476850797477888) }, { argument := 47738062764942476850797477888, coefficient := (-47738062764942476850797477888) }, { argument := 1137241044729750301817729863122944, coefficient := 1137241044729750301817729863122944 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 39614081257132168796771975168, coefficient := 39614081257132168796771975168 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 5996272065288560706542632960, coefficient := 5996272065288560706542632960 }, { argument := 143523673304648775621117214720, coefficient := 143523673304648775621117214720 }, { argument := 107352612781779070713908428800, coefficient := 107352612781779070713908428800 }, { argument := 124567716453091390161724375040, coefficient := 124567716453091390161724375040 }, { argument := 5996272065288560706542632960, coefficient := 5996272065288560706542632960 }, { argument := 124374288321953049493771386880, coefficient := 124374288321953049493771386880 }, { argument := 124954572715368071497630351360, coefficient := 124954572715368071497630351360 }, { argument := 5996272065288560706542632960, coefficient := 5996272065288560706542632960 }, { argument := 143523673304648775621117214720, coefficient := 143523673304648775621117214720 }] }

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

end TermShard11


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
