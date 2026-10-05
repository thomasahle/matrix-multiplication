import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 1, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1

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
def constantNumerator : ℤ := (-107051694108366836810190774337536)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    839081541, 749575755, 82507077, 6689763, 1433839203, 2593398123,
    749575755, 1433839203, 42368499, 42368499, 82507077, 82507077,
    2593398123, 82507077, 839081541, 6689763, 105417915, 20908045125,
    20908045125, 105417915, 380655967, 160572037, 1119100367, 27010419915,
    43601313, 72668855, 2223666963, 72668855, 43601313, 35622272721,
    2281802047, 160572037, 2223666963, 72668855, 2281802047, 72668855,
    2223666963, 72668855, 380655967, 2735395, 542524125, 542524125,
    2735395, 35954555, 1473064775, 30331544425, 1473064775, 35954555,
    372285841, 8879465, 3414162675, 100211105, 8879465, 6828323685,
    8879465, 8879465, 368117249, 2283291, 100211105, 368117249,
    372285841, 8879465, 2283291, 8879465
  ]
def negativeCoefficients : Array ℕ := #[
    7739161221900414078186160128, 6913616058171306401637335040, 6087947734755390603267145728, 7897878142385371593427648512, 105798659282370706970291208192, 191359005824878899232424067072,
    6913616058171306401637335040, 105798659282370706970291208192, 6252486862721752511463555072, 6252486862721752511463555072, 6087947734755390603267145728, 6087947734755390603267145728,
    191359005824878899232424067072, 6087947734755390603267145728, 7739161221900414078186160128, 7897878142385371593427648512, 121538581174316702933975040, 24105334843902851958177792000,
    24105334843902851958177792000, 121538581174316702933975040, 877732900422428580940611584, 23696250175465766794702094336, 20643758062843434264871043072, 124563575873858175223631708160,
    12868836195019283697581948928, 670251885157254359249059840, 20509707685811983393021231104, 21448060325032139495969914880, 12868836195019283697581948928, 328557474104086086903889133568,
    21045909193937786880420478976, 23696250175465766794702094336, 20509707685811983393021231104, 670251885157254359249059840, 21045909193937786880420478976, 670251885157254359249059840,
    20509707685811983393021231104, 21448060325032139495969914880, 877732900422428580940611584, 6307391438188092367831040, 1250975460961026249326592000, 1250975460961026249326592000,
    6307391438188092367831040, 82905559296139265950351360, 13586624454210772033286963200, 139879559342081684846883635200, 13586624454210772033286963200, 82905559296139265950351360,
    858432703899090801636933632, 81898609183230691869982720, 31490092545868299959166566400, 924284303639317808246947840, 81898609183230691869982720, 31490084867411079277565706240,
    81898609183230691869982720, 81898609183230691869982720, 3395282340710506682952712192, 84238569445608711637696512, 924284303639317808246947840, 3395282340710506682952712192,
    858432703899090801636933632, 81898609183230691869982720, 84238569445608711637696512, 81898609183230691869982720
  ]
def negativeScales : Array ℕ := #[
    29, 29, 26, 22, 30, 31,
    29, 30, 25, 25, 26, 26,
    31, 26, 29, 22, 26, 34,
    34, 26, 28, 27, 30, 34,
    25, 26, 31, 26, 25, 35,
    31, 27, 31, 26, 31, 26,
    31, 26, 28, 21, 29, 29,
    21, 25, 30, 34, 30, 25,
    28, 23, 31, 26, 23, 32,
    23, 23, 28, 21, 26, 28,
    28, 23, 21, 23
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    29644235776075759, 29481499048933198, 26298014535265933, 22673523670396474, 30417236096964944, 31272196551110202,
    29481499048933198, 30417236096964944, 25336488683080569, 25336488683080569, 26298014535265933, 26298014535265933,
    31272196551110202, 26298014535265933, 29644235776075759, 22673523670396474, 26651544822352109, 34283339126998601,
    34283339126998601, 26651544822352109, 28503912452548525, 27258645434059150, 30059692284831217, 34652797017643007,
    25377868244857474, 26114833839023678, 31050293586828967, 26114833839023678, 25377868244857474, 35052060513003155,
    31087526493027943, 27258645434059150, 31050293586828967, 26114833839023678, 31087526493027943, 26114833839023678,
    31050293586828967, 26114833839023678, 28503912452548525, 21383317747275837, 29015112051944484, 29015112051944484,
    21383317747275837, 25099671218176001, 30456173725308212, 34820099908982713, 30456173725308212, 25099671218176001,
    28471835506882499, 23082041324154209, 31668884654279649, 26578467150276789, 23082041324154209, 32668884302496830,
    23082041324154209, 23082041324154209, 28455590111276045, 21122683308651555, 26578467150276789, 28455590111276045,
    28471835506882499, 23082041324154209, 21122683308651555, 23082041324154209
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
noncomputable def negativeCeiling : ℝ := 128059077 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7739161221900414078186160128, coefficient := (-7739161221900414078186160128) }, { argument := 6913616058171306401637335040, coefficient := (-6913616058171306401637335040) }, { argument := 6087947734755390603267145728, coefficient := (-6087947734755390603267145728) }, { argument := 7897878142385371593427648512, coefficient := (-7897878142385371593427648512) }, { argument := 105798659282370706970291208192, coefficient := (-105798659282370706970291208192) }, { argument := 191359005824878899232424067072, coefficient := (-191359005824878899232424067072) }, { argument := 6913616058171306401637335040, coefficient := (-6913616058171306401637335040) }, { argument := 105798659282370706970291208192, coefficient := (-105798659282370706970291208192) }, { argument := 6252486862721752511463555072, coefficient := (-6252486862721752511463555072) }, { argument := 6252486862721752511463555072, coefficient := (-6252486862721752511463555072) }, { argument := 6087947734755390603267145728, coefficient := (-6087947734755390603267145728) }, { argument := 6087947734755390603267145728, coefficient := (-6087947734755390603267145728) }, { argument := 191359005824878899232424067072, coefficient := (-191359005824878899232424067072) }, { argument := 6087947734755390603267145728, coefficient := (-6087947734755390603267145728) }, { argument := 7739161221900414078186160128, coefficient := (-7739161221900414078186160128) }, { argument := 7897878142385371593427648512, coefficient := (-7897878142385371593427648512) }, { argument := 121538581174316702933975040, coefficient := (-121538581174316702933975040) }, { argument := 24105334843902851958177792000, coefficient := (-24105334843902851958177792000) }, { argument := 24105334843902851958177792000, coefficient := (-24105334843902851958177792000) }, { argument := 121538581174316702933975040, coefficient := (-121538581174316702933975040) }, { argument := 877732900422428580940611584, coefficient := (-877732900422428580940611584) }, { argument := 23696250175465766794702094336, coefficient := (-23696250175465766794702094336) }, { argument := 20643758062843434264871043072, coefficient := (-20643758062843434264871043072) }, { argument := 124563575873858175223631708160, coefficient := (-124563575873858175223631708160) }, { argument := 12868836195019283697581948928, coefficient := (-12868836195019283697581948928) }, { argument := 670251885157254359249059840, coefficient := (-670251885157254359249059840) }, { argument := 20509707685811983393021231104, coefficient := (-20509707685811983393021231104) }, { argument := 21448060325032139495969914880, coefficient := (-21448060325032139495969914880) }, { argument := 12868836195019283697581948928, coefficient := (-12868836195019283697581948928) }, { argument := 328557474104086086903889133568, coefficient := (-328557474104086086903889133568) }, { argument := 21045909193937786880420478976, coefficient := (-21045909193937786880420478976) }, { argument := 23696250175465766794702094336, coefficient := (-23696250175465766794702094336) }, { argument := 20509707685811983393021231104, coefficient := (-20509707685811983393021231104) }, { argument := 670251885157254359249059840, coefficient := (-670251885157254359249059840) }, { argument := 21045909193937786880420478976, coefficient := (-21045909193937786880420478976) }, { argument := 670251885157254359249059840, coefficient := (-670251885157254359249059840) }, { argument := 20509707685811983393021231104, coefficient := (-20509707685811983393021231104) }, { argument := 21448060325032139495969914880, coefficient := (-21448060325032139495969914880) }, { argument := 877732900422428580940611584, coefficient := (-877732900422428580940611584) }, { argument := 6307391438188092367831040, coefficient := (-6307391438188092367831040) }, { argument := 1250975460961026249326592000, coefficient := (-1250975460961026249326592000) }, { argument := 1250975460961026249326592000, coefficient := (-1250975460961026249326592000) }, { argument := 6307391438188092367831040, coefficient := (-6307391438188092367831040) }, { argument := 82905559296139265950351360, coefficient := (-82905559296139265950351360) }, { argument := 13586624454210772033286963200, coefficient := (-13586624454210772033286963200) }, { argument := 139879559342081684846883635200, coefficient := (-139879559342081684846883635200) }, { argument := 13586624454210772033286963200, coefficient := (-13586624454210772033286963200) }, { argument := 82905559296139265950351360, coefficient := (-82905559296139265950351360) }, { argument := 858432703899090801636933632, coefficient := (-858432703899090801636933632) }, { argument := 81898609183230691869982720, coefficient := (-81898609183230691869982720) }, { argument := 31490092545868299959166566400, coefficient := (-31490092545868299959166566400) }, { argument := 924284303639317808246947840, coefficient := (-924284303639317808246947840) }, { argument := 81898609183230691869982720, coefficient := (-81898609183230691869982720) }, { argument := 31490084867411079277565706240, coefficient := (-31490084867411079277565706240) }, { argument := 81898609183230691869982720, coefficient := (-81898609183230691869982720) }, { argument := 81898609183230691869982720, coefficient := (-81898609183230691869982720) }, { argument := 3395282340710506682952712192, coefficient := (-3395282340710506682952712192) }, { argument := 84238569445608711637696512, coefficient := (-84238569445608711637696512) }, { argument := 924284303639317808246947840, coefficient := (-924284303639317808246947840) }, { argument := 3395282340710506682952712192, coefficient := (-3395282340710506682952712192) }, { argument := 858432703899090801636933632, coefficient := (-858432703899090801636933632) }, { argument := 81898609183230691869982720, coefficient := (-81898609183230691869982720) }, { argument := 84238569445608711637696512, coefficient := (-84238569445608711637696512) }, { argument := 81898609183230691869982720, coefficient := (-81898609183230691869982720) }] }

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
def constantNumerator : ℤ := (-1903510881020428381029981084450816)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    24547603733, 40689558315, 601107069, 48738411, 10446266091, 18894257331,
    40689558315, 10446266091, 308676603, 308676603, 601107069, 601107069,
    18894257331, 601107069, 24547603733, 48738411, 6988098711, 25907313333,
    11185356259, 15904520665, 435793101, 726321835, 22225448151, 726321835,
    435793101, 356042963517, 22806505619, 25907313333, 22225448151, 726321835,
    22806505619, 726321835, 22225448151, 726321835, 6988098711, 169804905,
    33678228375, 33678228375, 169804905, 405772835, 16624588175, 342313144225,
    16624588175, 405772835, 20194930025, 363793325, 101284582245, 4105667525,
    363793325, 202569116205, 363793325, 363793325, 15081831845, 93546855,
    4105667525, 15081831845, 20194930025, 363793325, 93546855, 363793325,
    35954555, 1473064775, 30331544425, 1473064775
  ]
def negativeCoefficients : Array ℕ := #[
    28301460230343013525417361408, 46911866794317841178233405440, 22176936525481337058395947008, 28770079816840653481162309632, 385399194213094587258070106112, 697075058895534999970661793792,
    46911866794317841178233405440, 385399194213094587258070106112, 22776313188332184005920161792, 22776313188332184005920161792, 22176936525481337058395947008, 22176936525481337058395947008,
    697075058895534999970661793792, 22176936525481337058395947008, 28301460230343013525417361408, 28770079816840653481162309632, 32226917120909151659039391744, 477905578691254201350648496128,
    825333617132153162064436658176, 146693311161139923442278072320, 514493683407056516611596877824, 26796546010784193573520670720, 819974307929996323349732524032, 857489472345094194352661463040,
    514493683407056516611596877824, 13135666854486411689739832786944, 841411544738623678208549060608, 477905578691254201350648496128, 819974307929996323349732524032, 26796546010784193573520670720,
    841411544738623678208549060608, 26796546010784193573520670720, 819974307929996323349732524032, 857489472345094194352661463040, 32226917120909151659039391744, 195771726562222713109217280,
    38828353730598007046406144000, 38828353730598007046406144000, 195771726562222713109217280, 935648454913571715725393920, 153334761697521570089952870400, 1578640741146350443271972454400,
    153334761697521570089952870400, 935648454913571715725393920, 23283169109852989816202854400, 13421604723997685733287526400, 467092691821525355723206164480, 151472396170831024704244940800,
    13421604723997685733287526400, 467092580483895655839993692160, 13421604723997685733287526400, 13421604723997685733287526400, 556421384414875485685720023040, 13805079144683333897095741440,
    151472396170831024704244940800, 556421384414875485685720023040, 23283169109852989816202854400, 13421604723997685733287526400, 13805079144683333897095741440, 13421604723997685733287526400,
    82905559296139265950351360, 13586624454210772033286963200, 139879559342081684846883635200, 13586624454210772033286963200
  ]
def negativeScales : Array ℕ := #[
    34, 35, 29, 25, 33, 34,
    35, 33, 28, 28, 29, 29,
    34, 29, 34, 25, 32, 34,
    33, 33, 28, 29, 34, 29,
    28, 38, 34, 34, 34, 29,
    34, 29, 34, 29, 32, 27,
    34, 34, 27, 28, 33, 38,
    33, 28, 34, 28, 36, 31,
    28, 37, 28, 28, 33, 26,
    31, 33, 34, 28, 26, 28,
    25, 30, 34, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34514863148515977, 35243939568921089, 29163046745305956, 25538555880399099, 33282268307004954, 34137228761150225,
    35243939568921089, 33282268307004954, 28201520893120592, 28201520893120592, 29163046745305956, 29163046745305956,
    34137228761150225, 29163046745305956, 34514863148515977, 25538555880399099, 32702252841376265, 34592640360300171,
    33380892156536402, 33888717844612593, 28699068116633471, 29436033710728888, 34371493458534152, 29436033710728888,
    28699068116633471, 38373260384708340, 34408726364733134, 34592640360300171, 34371493458534152, 29436033710728888,
    34408726364733134, 29436033710728888, 34371493458534152, 29436033710728888, 32702252841376265, 27339302892412522,
    34971097211901790, 34971097211901790, 27339302892412522, 28596097044300573, 33952599562318741, 38316525734134283,
    33952599562318741, 28596097044300573, 34233274096015867, 28438543831286392, 36559623624500611, 31934969665475077,
    28438543831286392, 37559623280615408, 28438543831286392, 28438543831286392, 33812092619233149, 26479185815783841,
    31934969665475077, 33812092619233149, 34233274096015867, 28438543831286392, 26479185815783841, 28438543831286392,
    25099671218176001, 30456173725308212, 34820099908982713, 30456173725308212
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
noncomputable def negativeCeiling : ℝ := 2519002411 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 28301460230343013525417361408, coefficient := (-28301460230343013525417361408) }, { argument := 46911866794317841178233405440, coefficient := (-46911866794317841178233405440) }, { argument := 22176936525481337058395947008, coefficient := (-22176936525481337058395947008) }, { argument := 28770079816840653481162309632, coefficient := (-28770079816840653481162309632) }, { argument := 385399194213094587258070106112, coefficient := (-385399194213094587258070106112) }, { argument := 697075058895534999970661793792, coefficient := (-697075058895534999970661793792) }, { argument := 46911866794317841178233405440, coefficient := (-46911866794317841178233405440) }, { argument := 385399194213094587258070106112, coefficient := (-385399194213094587258070106112) }, { argument := 22776313188332184005920161792, coefficient := (-22776313188332184005920161792) }, { argument := 22776313188332184005920161792, coefficient := (-22776313188332184005920161792) }, { argument := 22176936525481337058395947008, coefficient := (-22176936525481337058395947008) }, { argument := 22176936525481337058395947008, coefficient := (-22176936525481337058395947008) }, { argument := 697075058895534999970661793792, coefficient := (-697075058895534999970661793792) }, { argument := 22176936525481337058395947008, coefficient := (-22176936525481337058395947008) }, { argument := 28301460230343013525417361408, coefficient := (-28301460230343013525417361408) }, { argument := 28770079816840653481162309632, coefficient := (-28770079816840653481162309632) }, { argument := 32226917120909151659039391744, coefficient := (-32226917120909151659039391744) }, { argument := 477905578691254201350648496128, coefficient := (-477905578691254201350648496128) }, { argument := 825333617132153162064436658176, coefficient := (-825333617132153162064436658176) }, { argument := 146693311161139923442278072320, coefficient := (-146693311161139923442278072320) }, { argument := 514493683407056516611596877824, coefficient := (-514493683407056516611596877824) }, { argument := 26796546010784193573520670720, coefficient := (-26796546010784193573520670720) }, { argument := 819974307929996323349732524032, coefficient := (-819974307929996323349732524032) }, { argument := 857489472345094194352661463040, coefficient := (-857489472345094194352661463040) }, { argument := 514493683407056516611596877824, coefficient := (-514493683407056516611596877824) }, { argument := 13135666854486411689739832786944, coefficient := (-13135666854486411689739832786944) }, { argument := 841411544738623678208549060608, coefficient := (-841411544738623678208549060608) }, { argument := 477905578691254201350648496128, coefficient := (-477905578691254201350648496128) }, { argument := 819974307929996323349732524032, coefficient := (-819974307929996323349732524032) }, { argument := 26796546010784193573520670720, coefficient := (-26796546010784193573520670720) }, { argument := 841411544738623678208549060608, coefficient := (-841411544738623678208549060608) }, { argument := 26796546010784193573520670720, coefficient := (-26796546010784193573520670720) }, { argument := 819974307929996323349732524032, coefficient := (-819974307929996323349732524032) }, { argument := 857489472345094194352661463040, coefficient := (-857489472345094194352661463040) }, { argument := 32226917120909151659039391744, coefficient := (-32226917120909151659039391744) }, { argument := 195771726562222713109217280, coefficient := (-195771726562222713109217280) }, { argument := 38828353730598007046406144000, coefficient := (-38828353730598007046406144000) }, { argument := 38828353730598007046406144000, coefficient := (-38828353730598007046406144000) }, { argument := 195771726562222713109217280, coefficient := (-195771726562222713109217280) }, { argument := 935648454913571715725393920, coefficient := (-935648454913571715725393920) }, { argument := 153334761697521570089952870400, coefficient := (-153334761697521570089952870400) }, { argument := 1578640741146350443271972454400, coefficient := (-1578640741146350443271972454400) }, { argument := 153334761697521570089952870400, coefficient := (-153334761697521570089952870400) }, { argument := 935648454913571715725393920, coefficient := (-935648454913571715725393920) }, { argument := 23283169109852989816202854400, coefficient := (-23283169109852989816202854400) }, { argument := 13421604723997685733287526400, coefficient := (-13421604723997685733287526400) }, { argument := 467092691821525355723206164480, coefficient := (-467092691821525355723206164480) }, { argument := 151472396170831024704244940800, coefficient := (-151472396170831024704244940800) }, { argument := 13421604723997685733287526400, coefficient := (-13421604723997685733287526400) }, { argument := 467092580483895655839993692160, coefficient := (-467092580483895655839993692160) }, { argument := 13421604723997685733287526400, coefficient := (-13421604723997685733287526400) }, { argument := 13421604723997685733287526400, coefficient := (-13421604723997685733287526400) }, { argument := 556421384414875485685720023040, coefficient := (-556421384414875485685720023040) }, { argument := 13805079144683333897095741440, coefficient := (-13805079144683333897095741440) }, { argument := 151472396170831024704244940800, coefficient := (-151472396170831024704244940800) }, { argument := 556421384414875485685720023040, coefficient := (-556421384414875485685720023040) }, { argument := 23283169109852989816202854400, coefficient := (-23283169109852989816202854400) }, { argument := 13421604723997685733287526400, coefficient := (-13421604723997685733287526400) }, { argument := 13805079144683333897095741440, coefficient := (-13805079144683333897095741440) }, { argument := 13421604723997685733287526400, coefficient := (-13421604723997685733287526400) }, { argument := 82905559296139265950351360, coefficient := (-82905559296139265950351360) }, { argument := 13586624454210772033286963200, coefficient := (-13586624454210772033286963200) }, { argument := 139879559342081684846883635200, coefficient := (-139879559342081684846883635200) }, { argument := 13586624454210772033286963200, coefficient := (-13586624454210772033286963200) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1
