import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 10, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10

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
def constantNumerator : ℤ := (-11923874010356417649142833069686784)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    5023777, 3507, 32915423, 5649, 175, 5649,
    3773, 5052449, 3507, 21, 227206246961, 9540128708329,
    57315291525, 101821215375, 4724485084395, 656869459185, 9540131124969, 4724485084395,
    57315291525, 114605411535, 98373451185, 114605411535, 656869459185, 98373451185,
    227203830321, 101821215375, 61533986859997, 3068624292302455, 630800359257, 61616901521634457,
    647222727261, 20615192517, 630800359257, 358750213527, 647222727261, 10104664267731,
    12370201155, 3068625630230445, 630800359257, 20615192517, 12370201155, 20615192517,
    317461165581, 358750213527, 30767115516577, 1425, 5985, 25935,
    855, 855, 1995, 25935, 25935, 855,
    320055, 12825, 5985, 25935, 1995, 12825,
    1995, 25935, 25935, 855
  ]
def negativeCoefficients : Array ℕ := #[
    23724116122211417622726049792, 67835245590216072251112947712, 310877380689353252137458466816, 109267551280048643326643011584, 3384992294920961689177292800, 109267551280048643326643011584,
    72980433878495934018662432768, 23859515814008256090293141504, 67835245590216072251112947712, 3249592603124123221610201088, 261950968102350973240592039936, 10999019544549646264116239663104,
    132160064283966129881009356800, 117391868831042820642963456000, 5446960451993289816702210539520, 1514637850427712118346345349120, 10999022330745871157206915743744, 5446960451993289816702210539520,
    132160064283966129881009356800, 132131043503019096063250268160, 113416867353578413610300866560, 132131043503019096063250268160, 1514637850427712118346345349120, 113416867353578413610300866560,
    261948181906126080149915959296, 117391868831042820642963456000, 138562220146651743208400224256, 13819855219353388334985175367680, 727263299301120053002824056832, 138748927366278744260853509390336,
    746197000529499075380810612736, 23767698774459452806599278592, 727263299301120053002824056832, 413610835957576466826214244352, 746197000529499075380810612736, 11649884731099468141791811731456,
    456379869693182601069550632960, 13819861244845385547541873950720, 727263299301120053002824056832, 23767698774459452806599278592, 456379869693182601069550632960, 23767698774459452806599278592,
    732015609351779804308530266112, 413610835957576466826214244352, 138562769975721182747208712192, 107669955809427910872268800, 1808855257598388902654115840, 3919186391463175955750584320,
    129203946971313493046722560, 2067263151541015888747560960, 150737938133199075221176320, 3919186391463175955750584320, 3919186391463175955750584320, 2067263151541015888747560960,
    48365344149595017563823144960, 3876118409139404791401676800, 1808855257598388902654115840, 3919186391463175955750584320, 150737938133199075221176320, 3876118409139404791401676800,
    150737938133199075221176320, 3919186391463175955750584320, 3919186391463175955750584320, 129203946971313493046722560
  ]
def negativeScales : Array ℕ := #[
    22, 11, 24, 12, 7, 12,
    11, 22, 11, 4, 37, 43,
    35, 36, 42, 39, 43, 42,
    35, 36, 36, 36, 39, 36,
    37, 36, 45, 51, 39, 55,
    39, 34, 39, 38, 39, 43,
    33, 51, 39, 34, 33, 34,
    38, 38, 44, 10, 12, 14,
    9, 9, 10, 14, 14, 9,
    18, 13, 12, 14, 10, 13,
    10, 14, 14, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    22260340995310396, 11776021715645854, 24972260417439156, 12463779785335462, 7451211111832378, 12463779785335462,
    11881496387932734, 22268551423273385, 11776021715645854, 4392317422778766, 37725211545703887, 43117145868780120,
    35738201045518238, 36567247235112235, 42103294239057115, 39256815733488458, 43117146234233691, 42103294239057115,
    35738201045518238, 36737884212027813, 36517549965539367, 36737884212027813, 39256815733488458, 36517549965539367,
    37725196200645631, 36567247235112235, 45806448703762239, 51446513443239150, 39198392525541510, 55774175655160102,
    39235471312732594, 34262988882911841, 39198392525541510, 38384188734237127, 39235471312732594, 43200086621821791,
    33526149909411774, 51446514072257717, 39198392525541510, 34262988882911841, 33526149909411774, 34262988882911841,
    38207789164306080, 38384188734237127, 44806454428512528, 10476746203939589, 12547135531832084, 14662612749280074,
    9739780609952834, 9739780609952834, 10962173043893966, 14662612749280074, 14662612749280074, 9739780609952834,
    18287960321452706, 13646671205401350, 12547135531832084, 14662612749280074, 10962173043893966, 13646671205401350,
    10962173043893966, 14662612749280074, 14662612749280074, 9739780609952834
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
noncomputable def negativeCeiling : ℝ := 27710758591 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 23724116122211417622726049792, coefficient := (-23724116122211417622726049792) }, { argument := 67835245590216072251112947712, coefficient := (-67835245590216072251112947712) }, { argument := 310877380689353252137458466816, coefficient := (-310877380689353252137458466816) }, { argument := 109267551280048643326643011584, coefficient := (-109267551280048643326643011584) }, { argument := 3384992294920961689177292800, coefficient := (-3384992294920961689177292800) }, { argument := 109267551280048643326643011584, coefficient := (-109267551280048643326643011584) }, { argument := 72980433878495934018662432768, coefficient := (-72980433878495934018662432768) }, { argument := 23859515814008256090293141504, coefficient := (-23859515814008256090293141504) }, { argument := 67835245590216072251112947712, coefficient := (-67835245590216072251112947712) }, { argument := 3249592603124123221610201088, coefficient := (-3249592603124123221610201088) }, { argument := 261950968102350973240592039936, coefficient := (-261950968102350973240592039936) }, { argument := 10999019544549646264116239663104, coefficient := (-10999019544549646264116239663104) }, { argument := 132160064283966129881009356800, coefficient := (-132160064283966129881009356800) }, { argument := 117391868831042820642963456000, coefficient := (-117391868831042820642963456000) }, { argument := 5446960451993289816702210539520, coefficient := (-5446960451993289816702210539520) }, { argument := 1514637850427712118346345349120, coefficient := (-1514637850427712118346345349120) }, { argument := 10999022330745871157206915743744, coefficient := (-10999022330745871157206915743744) }, { argument := 5446960451993289816702210539520, coefficient := (-5446960451993289816702210539520) }, { argument := 132160064283966129881009356800, coefficient := (-132160064283966129881009356800) }, { argument := 132131043503019096063250268160, coefficient := (-132131043503019096063250268160) }, { argument := 113416867353578413610300866560, coefficient := (-113416867353578413610300866560) }, { argument := 132131043503019096063250268160, coefficient := (-132131043503019096063250268160) }, { argument := 1514637850427712118346345349120, coefficient := (-1514637850427712118346345349120) }, { argument := 113416867353578413610300866560, coefficient := (-113416867353578413610300866560) }, { argument := 261948181906126080149915959296, coefficient := (-261948181906126080149915959296) }, { argument := 117391868831042820642963456000, coefficient := (-117391868831042820642963456000) }, { argument := 138562220146651743208400224256, coefficient := (-138562220146651743208400224256) }, { argument := 13819855219353388334985175367680, coefficient := (-13819855219353388334985175367680) }, { argument := 727263299301120053002824056832, coefficient := (-727263299301120053002824056832) }, { argument := 138748927366278744260853509390336, coefficient := (-138748927366278744260853509390336) }, { argument := 746197000529499075380810612736, coefficient := (-746197000529499075380810612736) }, { argument := 23767698774459452806599278592, coefficient := (-23767698774459452806599278592) }, { argument := 727263299301120053002824056832, coefficient := (-727263299301120053002824056832) }, { argument := 413610835957576466826214244352, coefficient := (-413610835957576466826214244352) }, { argument := 746197000529499075380810612736, coefficient := (-746197000529499075380810612736) }, { argument := 11649884731099468141791811731456, coefficient := (-11649884731099468141791811731456) }, { argument := 456379869693182601069550632960, coefficient := (-456379869693182601069550632960) }, { argument := 13819861244845385547541873950720, coefficient := (-13819861244845385547541873950720) }, { argument := 727263299301120053002824056832, coefficient := (-727263299301120053002824056832) }, { argument := 23767698774459452806599278592, coefficient := (-23767698774459452806599278592) }, { argument := 456379869693182601069550632960, coefficient := (-456379869693182601069550632960) }, { argument := 23767698774459452806599278592, coefficient := (-23767698774459452806599278592) }, { argument := 732015609351779804308530266112, coefficient := (-732015609351779804308530266112) }, { argument := 413610835957576466826214244352, coefficient := (-413610835957576466826214244352) }, { argument := 138562769975721182747208712192, coefficient := (-138562769975721182747208712192) }, { argument := 107669955809427910872268800, coefficient := (-107669955809427910872268800) }, { argument := 1808855257598388902654115840, coefficient := (-1808855257598388902654115840) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 129203946971313493046722560, coefficient := (-129203946971313493046722560) }, { argument := 2067263151541015888747560960, coefficient := (-2067263151541015888747560960) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 2067263151541015888747560960, coefficient := (-2067263151541015888747560960) }, { argument := 48365344149595017563823144960, coefficient := (-48365344149595017563823144960) }, { argument := 3876118409139404791401676800, coefficient := (-3876118409139404791401676800) }, { argument := 1808855257598388902654115840, coefficient := (-1808855257598388902654115840) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 3876118409139404791401676800, coefficient := (-3876118409139404791401676800) }, { argument := 150737938133199075221176320, coefficient := (-150737938133199075221176320) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 3919186391463175955750584320, coefficient := (-3919186391463175955750584320) }, { argument := 129203946971313493046722560, coefficient := (-129203946971313493046722560) }] }

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
def constantNumerator : ℤ := (-3872142191486451647882552267505664)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    180311072885871, 76012677, 3246792774752663, 1880909433, 59839767, 3246741862394507,
    30728529, 30728529, 1039918113, 56605185, 1880909433, 1039918113,
    180413211093837, 59839767, 56605185, 76012677, 465, 1953,
    8463, 279, 279, 651, 8463, 8463,
    279, 104439, 4185, 1953, 8463, 651,
    4185, 651, 8463, 8463, 279, 38331179,
    1415519445, 11324152787, 306652205, 15380772902667, 1425, 465,
    426404977532225, 4695, 123046182382183, 9405, 4215, 1425,
    465, 227205680591, 9540128254231, 57315036795, 101820632433, 4724476521237,
    656862051087, 9540130670871, 4724476521237, 57315036795, 114604913457, 98372960847,
    114604913457, 656862051087, 98372960847, 227203263951
  ]
def negativeCoefficients : Array ℕ := #[
    406024440329791490215020331008, 2804372797953096677603672064, 14622254730525311839931463630848, 69393309872754285873469587456, 2207697734558820788751826944, 14622025441648091925098604265472,
    2267365240898248377637011456, 2267365240898248377637011456, 38366206576251939653173641216, 2088362721879965610981457920, 69393309872754285873469587456, 38366206576251939653173641216,
    406254435127459474128110616576, 2207697734558820788751826944, 2088362721879965610981457920, 2804372797953096677603672064, 4391800829068770048737280, 73782253928355336818786304,
    159861550178103229774036992, 5270160994882524058484736, 84322575918120384935755776, 6148521160696278068232192, 159861550178103229774036992, 159861550178103229774036992,
    84322575918120384935755776, 1972796932417691505892786176, 158104829846475721754542080, 73782253928355336818786304, 159861550178103229774036992, 6148521160696278068232192,
    158104829846475721754542080, 6148521160696278068232192, 159861550178103229774036992, 159861550178103229774036992, 5270160994882524058484736, 2828341796226200068010541056,
    104446899733097534378716692480, 104446874156686876180423376896, 2828367372636858266303856640, 138537686226242646685111025664, 107669955809427910872268800, 4391800829068770048737280,
    480089324480763307258963558400, 88686042548291937113210880, 138537685281440362158402568192, 88827713542778026469621760, 79619098901182218302914560, 107669955809427910872268800,
    4391800829068770048737280, 261950315122198409060670242816, 10999019021010296865156241555456, 132159476916576392876748963840, 117391196744675082118373572608, 5446950579344284270543673229312,
    1514620768516727248398606925824, 10999021807206521758246917636096, 5446950579344284270543673229312, 132159476916576392876748963840, 132130469258181924494122156032, 113416302032353687698168348672,
    132130469258181924494122156032, 1514620768516727248398606925824, 113416302032353687698168348672, 261947528925973515969994162176
  ]
def negativeScales : Array ℕ := #[
    47, 26, 51, 30, 25, 51,
    24, 24, 29, 25, 30, 29,
    47, 25, 25, 26, 8, 10,
    13, 8, 8, 9, 13, 13,
    8, 16, 12, 10, 13, 9,
    12, 9, 13, 13, 8, 25,
    30, 33, 28, 43, 10, 8,
    48, 12, 46, 13, 12, 10,
    8, 37, 43, 35, 36, 42,
    39, 43, 42, 35, 36, 36,
    36, 39, 36, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    47357481323679291, 26179736708029241, 51527936731440785, 30808783238596729, 25834601223267762, 51527914108628791,
    24873075372468708, 24873075372468708, 29953822794797077, 25754430873544240, 30808783238596729, 29953822794797077,
    47358298314919416, 25834601223267762, 25754430873544240, 26179736708029241, 8861086908132560, 10931476241484805,
    13046953451306728, 8124121311829188, 8124121311829188, 9346513733165637, 13046953451306728, 13046953451306728,
    8124121311829188, 16672301023545835, 12031011907437707, 10931476241484805, 13046953451306728, 9346513733165637,
    12031011907437707, 9346513733165637, 13046953451306728, 13046953451306728, 8124121311829188, 25192015037807678,
    30398684421677392, 33398684068397731, 28192028083894976, 43806193236581545, 10476746203939589, 8861086908132560,
    48599217607564963, 12196909442541137, 46806193226742623, 13199212228410558, 12041316915829445, 10476746203939589,
    8861086908132560, 37725207949410994, 43117145800109668, 35738194633642523, 36567238975439269, 42103291624161194,
    39256799462848432, 43117146165563256, 42103291624161194, 35738194633642523, 36737877942025244, 36517542774473531,
    36737877942025244, 39256799462848432, 36517542774473531, 37725192604314487
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
noncomputable def negativeCeiling : ℝ := 38190626571 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 406024440329791490215020331008, coefficient := (-406024440329791490215020331008) }, { argument := 2804372797953096677603672064, coefficient := (-2804372797953096677603672064) }, { argument := 14622254730525311839931463630848, coefficient := (-14622254730525311839931463630848) }, { argument := 69393309872754285873469587456, coefficient := (-69393309872754285873469587456) }, { argument := 2207697734558820788751826944, coefficient := (-2207697734558820788751826944) }, { argument := 14622025441648091925098604265472, coefficient := (-14622025441648091925098604265472) }, { argument := 2267365240898248377637011456, coefficient := (-2267365240898248377637011456) }, { argument := 2267365240898248377637011456, coefficient := (-2267365240898248377637011456) }, { argument := 38366206576251939653173641216, coefficient := (-38366206576251939653173641216) }, { argument := 2088362721879965610981457920, coefficient := (-2088362721879965610981457920) }, { argument := 69393309872754285873469587456, coefficient := (-69393309872754285873469587456) }, { argument := 38366206576251939653173641216, coefficient := (-38366206576251939653173641216) }, { argument := 406254435127459474128110616576, coefficient := (-406254435127459474128110616576) }, { argument := 2207697734558820788751826944, coefficient := (-2207697734558820788751826944) }, { argument := 2088362721879965610981457920, coefficient := (-2088362721879965610981457920) }, { argument := 2804372797953096677603672064, coefficient := (-2804372797953096677603672064) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 73782253928355336818786304, coefficient := (-73782253928355336818786304) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 5270160994882524058484736, coefficient := (-5270160994882524058484736) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 1972796932417691505892786176, coefficient := (-1972796932417691505892786176) }, { argument := 158104829846475721754542080, coefficient := (-158104829846475721754542080) }, { argument := 73782253928355336818786304, coefficient := (-73782253928355336818786304) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 158104829846475721754542080, coefficient := (-158104829846475721754542080) }, { argument := 6148521160696278068232192, coefficient := (-6148521160696278068232192) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 159861550178103229774036992, coefficient := (-159861550178103229774036992) }, { argument := 5270160994882524058484736, coefficient := (-5270160994882524058484736) }, { argument := 2828341796226200068010541056, coefficient := (-2828341796226200068010541056) }, { argument := 104446899733097534378716692480, coefficient := (-104446899733097534378716692480) }, { argument := 104446874156686876180423376896, coefficient := (-104446874156686876180423376896) }, { argument := 2828367372636858266303856640, coefficient := (-2828367372636858266303856640) }, { argument := 138537686226242646685111025664, coefficient := (-138537686226242646685111025664) }, { argument := 107669955809427910872268800, coefficient := (-107669955809427910872268800) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 480089324480763307258963558400, coefficient := (-480089324480763307258963558400) }, { argument := 88686042548291937113210880, coefficient := (-88686042548291937113210880) }, { argument := 138537685281440362158402568192, coefficient := (-138537685281440362158402568192) }, { argument := 88827713542778026469621760, coefficient := (-88827713542778026469621760) }, { argument := 79619098901182218302914560, coefficient := (-79619098901182218302914560) }, { argument := 107669955809427910872268800, coefficient := (-107669955809427910872268800) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 261950315122198409060670242816, coefficient := (-261950315122198409060670242816) }, { argument := 10999019021010296865156241555456, coefficient := (-10999019021010296865156241555456) }, { argument := 132159476916576392876748963840, coefficient := (-132159476916576392876748963840) }, { argument := 117391196744675082118373572608, coefficient := (-117391196744675082118373572608) }, { argument := 5446950579344284270543673229312, coefficient := (-5446950579344284270543673229312) }, { argument := 1514620768516727248398606925824, coefficient := (-1514620768516727248398606925824) }, { argument := 10999021807206521758246917636096, coefficient := (-10999021807206521758246917636096) }, { argument := 5446950579344284270543673229312, coefficient := (-5446950579344284270543673229312) }, { argument := 132159476916576392876748963840, coefficient := (-132159476916576392876748963840) }, { argument := 132130469258181924494122156032, coefficient := (-132130469258181924494122156032) }, { argument := 113416302032353687698168348672, coefficient := (-113416302032353687698168348672) }, { argument := 132130469258181924494122156032, coefficient := (-132130469258181924494122156032) }, { argument := 1514620768516727248398606925824, coefficient := (-1514620768516727248398606925824) }, { argument := 113416302032353687698168348672, coefficient := (-113416302032353687698168348672) }, { argument := 261947528925973515969994162176, coefficient := (-261947528925973515969994162176) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
