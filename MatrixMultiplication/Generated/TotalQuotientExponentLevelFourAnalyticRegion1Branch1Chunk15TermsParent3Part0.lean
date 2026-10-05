import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 15, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-9477694729068591698999200509329408)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2082077, 751, 66838411, 317, 31, 317,
    633, 260971, 751, 31, 251624833601303, 17680689361727721,
    3724017227, 9604955033, 8036875345, 224958322931, 8838764942588117, 8036875345,
    7258242221, 3725590091, 3724017227, 7255096493, 224958322931, 7255096493,
    125811607299883, 9604955033, 38133293083415, 10715278150508701, 53891030103, 105724011719613101,
    17054039249, 2046397547, 53890915415, 107101495093, 17054039249, 1652906137663,
    105736924227, 5357648407436333, 53890915415, 2046397547, 105736924227, 2046397547,
    53890915415, 53891718231, 38133293083415, 105, 3045, 2695,
    175, 105, 175, 5355, 175, 105,
    85785, 5495, 3045, 5355, 175, 5495,
    175, 5355, 175, 105
  ]
def negativeCoefficients : Array ℕ := #[
    9832330639553782297596526592, 116211621187915073306155286528, 315635471874665806217196077056, 98106748113366386785755594752, 4797017652230848565234106368, 98106748113366386785755594752,
    97952005608455714251393204224, 9859205627207793448507670528, 116211621187915073306155286528, 4797017652230848565234106368, 141652188355498906482991169536, 9953343252641307132115342589952,
    68695992712554528012429688832, 88590073666619740387136241664, 1186033461132169264589082460160, 2074874305179531889765670453248, 9951564625463811798000371499008, 1186033461132169264589082460160,
    66945468337890101815114989568, 68725006932225279112622637056, 68695992712554528012429688832, 66916454118219350714922041344, 2074874305179531889765670453248, 66916454118219350714922041344,
    141651276938659063300454612992, 88590073666619740387136241664, 85868542260438853220218961920, 12064330671450550844376349671424, 497057020089309148508244148224, 119034654946140878423495775617024,
    314591497449300842285455376384, 18874685911288006808726142976, 497055962279216985707716280320, 493918467473057593177063555072, 314591497449300842285455376384, 7622684124833272385618525028352,
    487625495089172040506784350208, 12064351685656200314704661315584, 497055962279216985707716280320, 18874685911288006808726142976, 487625495089172040506784350208, 18874685911288006808726142976,
    497055962279216985707716280320, 497063366949862125311411355648, 85868542260438853220218961920, 126937211059536063344148480, 1840589560363272918490152960, 3258055083861425625833144320,
    105781009216280052786790400, 2030995376952577013506375680, 105781009216280052786790400, 3236898882018169615275786240, 3384992294920961689177292800, 2030995376952577013506375680,
    51853850717820481876084654080, 3321523689391193657505218560, 1840589560363272918490152960, 3236898882018169615275786240, 105781009216280052786790400, 3321523689391193657505218560,
    105781009216280052786790400, 3236898882018169615275786240, 3384992294920961689177292800, 126937211059536063344148480
  ]
def negativeScales : Array ℕ := #[
    20, 9, 25, 8, 4, 8,
    9, 17, 9, 4, 47, 53,
    31, 33, 32, 37, 52, 32,
    32, 31, 31, 32, 37, 32,
    46, 33, 45, 53, 35, 56,
    33, 30, 35, 36, 33, 40,
    36, 52, 35, 30, 36, 30,
    35, 35, 45, 6, 11, 11,
    7, 6, 7, 12, 7, 6,
    16, 12, 11, 12, 7, 12,
    7, 12, 7, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    20989592013168019, 9552669097515714, 25994174121309653, 8308339030139408, 4954196321574415, 8308339030139408,
    9306061689428342, 17993529994224486, 9552669097515714, 4954196321574415, 47838267642902623, 53973024059320187,
    31794212601261879, 33161131713705303, 32903987564001717, 37710866788095752, 52972766231725584, 32903987564001717,
    32756973057276911, 31794821804688734, 31794212601261879, 32756347656551189, 37710866788095752, 32756347656551189,
    46838258360301092, 33161131713705303, 45116116357045801, 53250518818623003, 35649326112357917, 56553080687580768,
    33989394450872125, 30930439301435900, 35649323042088436, 36640187663438097, 33989394450872125, 40588141940371025,
    36621688309771453, 52250521331573344, 35649323042088436, 30930439301435900, 36621688309771453, 30930439301435900,
    35649323042088436, 35649344533837587, 45116116357045801, 6714245517766967, 11572226512796267, 11396069557639874,
    7451211111832378, 6714245517766967, 7451211111832378, 12386670859637623, 7451211111832378, 6714245517766967,
    16388437785811811, 12423903765836611, 11572226512796267, 12386670859637623, 7451211111832378, 12423903765836611,
    7451211111832378, 12386670859637623, 7451211111832378, 6714245517766967
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
noncomputable def negativeCeiling : ℝ := 23672589117 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 9832330639553782297596526592, coefficient := (-9832330639553782297596526592) }, { argument := 116211621187915073306155286528, coefficient := (-116211621187915073306155286528) }, { argument := 315635471874665806217196077056, coefficient := (-315635471874665806217196077056) }, { argument := 98106748113366386785755594752, coefficient := (-98106748113366386785755594752) }, { argument := 4797017652230848565234106368, coefficient := (-4797017652230848565234106368) }, { argument := 98106748113366386785755594752, coefficient := (-98106748113366386785755594752) }, { argument := 97952005608455714251393204224, coefficient := (-97952005608455714251393204224) }, { argument := 9859205627207793448507670528, coefficient := (-9859205627207793448507670528) }, { argument := 116211621187915073306155286528, coefficient := (-116211621187915073306155286528) }, { argument := 4797017652230848565234106368, coefficient := (-4797017652230848565234106368) }, { argument := 141652188355498906482991169536, coefficient := (-141652188355498906482991169536) }, { argument := 9953343252641307132115342589952, coefficient := (-9953343252641307132115342589952) }, { argument := 68695992712554528012429688832, coefficient := (-68695992712554528012429688832) }, { argument := 88590073666619740387136241664, coefficient := (-88590073666619740387136241664) }, { argument := 1186033461132169264589082460160, coefficient := (-1186033461132169264589082460160) }, { argument := 2074874305179531889765670453248, coefficient := (-2074874305179531889765670453248) }, { argument := 9951564625463811798000371499008, coefficient := (-9951564625463811798000371499008) }, { argument := 1186033461132169264589082460160, coefficient := (-1186033461132169264589082460160) }, { argument := 66945468337890101815114989568, coefficient := (-66945468337890101815114989568) }, { argument := 68725006932225279112622637056, coefficient := (-68725006932225279112622637056) }, { argument := 68695992712554528012429688832, coefficient := (-68695992712554528012429688832) }, { argument := 66916454118219350714922041344, coefficient := (-66916454118219350714922041344) }, { argument := 2074874305179531889765670453248, coefficient := (-2074874305179531889765670453248) }, { argument := 66916454118219350714922041344, coefficient := (-66916454118219350714922041344) }, { argument := 141651276938659063300454612992, coefficient := (-141651276938659063300454612992) }, { argument := 88590073666619740387136241664, coefficient := (-88590073666619740387136241664) }, { argument := 85868542260438853220218961920, coefficient := (-85868542260438853220218961920) }, { argument := 12064330671450550844376349671424, coefficient := (-12064330671450550844376349671424) }, { argument := 497057020089309148508244148224, coefficient := (-497057020089309148508244148224) }, { argument := 119034654946140878423495775617024, coefficient := (-119034654946140878423495775617024) }, { argument := 314591497449300842285455376384, coefficient := (-314591497449300842285455376384) }, { argument := 18874685911288006808726142976, coefficient := (-18874685911288006808726142976) }, { argument := 497055962279216985707716280320, coefficient := (-497055962279216985707716280320) }, { argument := 493918467473057593177063555072, coefficient := (-493918467473057593177063555072) }, { argument := 314591497449300842285455376384, coefficient := (-314591497449300842285455376384) }, { argument := 7622684124833272385618525028352, coefficient := (-7622684124833272385618525028352) }, { argument := 487625495089172040506784350208, coefficient := (-487625495089172040506784350208) }, { argument := 12064351685656200314704661315584, coefficient := (-12064351685656200314704661315584) }, { argument := 497055962279216985707716280320, coefficient := (-497055962279216985707716280320) }, { argument := 18874685911288006808726142976, coefficient := (-18874685911288006808726142976) }, { argument := 487625495089172040506784350208, coefficient := (-487625495089172040506784350208) }, { argument := 18874685911288006808726142976, coefficient := (-18874685911288006808726142976) }, { argument := 497055962279216985707716280320, coefficient := (-497055962279216985707716280320) }, { argument := 497063366949862125311411355648, coefficient := (-497063366949862125311411355648) }, { argument := 85868542260438853220218961920, coefficient := (-85868542260438853220218961920) }, { argument := 126937211059536063344148480, coefficient := (-126937211059536063344148480) }, { argument := 1840589560363272918490152960, coefficient := (-1840589560363272918490152960) }, { argument := 3258055083861425625833144320, coefficient := (-3258055083861425625833144320) }, { argument := 105781009216280052786790400, coefficient := (-105781009216280052786790400) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 105781009216280052786790400, coefficient := (-105781009216280052786790400) }, { argument := 3236898882018169615275786240, coefficient := (-3236898882018169615275786240) }, { argument := 3384992294920961689177292800, coefficient := (-3384992294920961689177292800) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 51853850717820481876084654080, coefficient := (-51853850717820481876084654080) }, { argument := 3321523689391193657505218560, coefficient := (-3321523689391193657505218560) }, { argument := 1840589560363272918490152960, coefficient := (-1840589560363272918490152960) }, { argument := 3236898882018169615275786240, coefficient := (-3236898882018169615275786240) }, { argument := 105781009216280052786790400, coefficient := (-105781009216280052786790400) }, { argument := 3321523689391193657505218560, coefficient := (-3321523689391193657505218560) }, { argument := 105781009216280052786790400, coefficient := (-105781009216280052786790400) }, { argument := 3236898882018169615275786240, coefficient := (-3236898882018169615275786240) }, { argument := 3384992294920961689177292800, coefficient := (-3384992294920961689177292800) }, { argument := 126937211059536063344148480, coefficient := (-126937211059536063344148480) }] }

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


end Parent3

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3021661331049695760001736552480768)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    20770189472415, 3365489141, 25764569305391911, 35214508329, 1559616919, 3220571156802251,
    1559616919, 3037148737, 57377485599, 3037148737, 35214508329, 57377485599,
    664649007657633, 3037148737, 3037148737, 3365489141, 87, 2523,
    2233, 145, 87, 145, 4437, 145,
    87, 71079, 4553, 2523, 4437, 145,
    4553, 145, 4437, 145, 87, 1619799013,
    16189816001, 32379624089, 1619799013, 1192112027371, 105, 87,
    279187491391315, 585, 76291726523885, 2343, 2343, 1677,
    87, 251624856301801, 17680687137410839, 3724018101, 9604957287, 8036877231,
    224958375693, 8838763830052651, 8036877231, 7258243923, 3725590965, 3724018101,
    7255098195, 224958375693, 7255098195, 125811618650325
  ]
def negativeCoefficients : Array ℕ := #[
    374162470273531171631907471360, 3880144804179724971976687616, 14504163090390541167223459807232, 40599563926661024706780463104, 3596231769727549974027173888, 14504163061694784847670983786496,
    3596231769727549974027173888, 3501594091576824974710669312, 132303474054713549044473397248, 3501594091576824974710669312, 40599563926661024706780463104, 132303474054713549044473397248,
    374164127902385740155501674496, 3501594091576824974710669312, 3501594091576824974710669312, 3880144804179724971976687616, 6573534144154546137464832, 95316245090240918993240064,
    168720709699966684194930688, 5477945120128788447887360, 105176546306472738199437312, 5477945120128788447887360, 167625120675940926505353216, 175294243844121230332395520,
    105176546306472738199437312, 2685288697887132097154383872, 172007476772043957263663104, 95316245090240918993240064, 167625120675940926505353216, 5477945120128788447887360,
    172007476772043957263663104, 5477945120128788447887360, 167625120675940926505353216, 175294243844121230332395520, 6573534144154546137464832, 3735002230457291369533669376,
    149324696185447411089626103808, 149324659693175947273705619456, 3735002230457291369533669376, 85900724516030754052957536256, 126937211059536063344148480, 6573534144154546137464832,
    314337170549107448462505410560, 176805401118639516800778240, 85896847786105068025272074240, 177032074709817259771035648, 177032074709817259771035648, 126710537468358320373891072,
    6573534144154546137464832, 141652201134743198223577382912, 9953342000462222015977402400768, 68696008835008848434577801216, 88590094456100311457800912896, 1186033739456643848718797242368,
    2074874791823087298297351634944, 9951563372860234269485090996224, 1186033739456643848718797242368, 66945484036069308541943414784, 68725023054679599534770749440, 68696008835008848434577801216,
    66916469816398557441750466560, 2074874791823087298297351634944, 66916469816398557441750466560, 141651289718120653723061452800
  ]
def negativeScales : Array ℕ := #[
    44, 31, 54, 35, 30, 51,
    30, 31, 35, 31, 35, 35,
    49, 31, 31, 31, 6, 11,
    11, 7, 6, 7, 12, 7,
    6, 16, 12, 11, 12, 7,
    12, 7, 12, 7, 6, 30,
    33, 34, 30, 40, 6, 6,
    47, 9, 46, 11, 11, 10,
    6, 47, 53, 31, 33, 32,
    37, 52, 32, 32, 31, 31,
    32, 37, 32, 46
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    44239579610511084, 31648169055724972, 54516237994012753, 35035450888586099, 30538544564531076, 51516237991158454,
    30538544564531076, 31500070416715775, 35739765696641504, 31500070416715775, 35035450888586099, 35739765696641504,
    49239586001979552, 31500070416715775, 31500070416715775, 31648169055724972, 6442943495848765, 11300924490976301,
    11124767535822474, 7179909090014935, 6442943495848765, 7179909090014935, 12115368837820224, 7179909090014935,
    6442943495848765, 16117135763994412, 12152601744019200, 11300924490976301, 12115368837820224, 7179909090014935,
    12152601744019200, 7179909090014935, 12115368837820224, 7179909090014935, 6442943495848765, 30593167666522473,
    33914367543861130, 34914367191292318, 30593167666522473, 40116656956443606, 6714245517766967, 6442943495848765,
    47988227653066380, 9192292814470767, 46116591845639481, 11194141238863136, 11194141238863136, 10711666973659367,
    6442943495848765, 47838267773056292, 53973023877822063, 31794212939851970, 33161132052263290, 32903987902556521,
    37710867126467171, 52972766050133482, 32903987902556521, 32756973395577371, 31794822143135880, 31794212939851970,
    32756347994998332, 37710867126467171, 32756347994998332, 46838258490457812
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
noncomputable def negativeCeiling : ℝ := 35479948401 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 374162470273531171631907471360, coefficient := (-374162470273531171631907471360) }, { argument := 3880144804179724971976687616, coefficient := (-3880144804179724971976687616) }, { argument := 14504163090390541167223459807232, coefficient := (-14504163090390541167223459807232) }, { argument := 40599563926661024706780463104, coefficient := (-40599563926661024706780463104) }, { argument := 3596231769727549974027173888, coefficient := (-3596231769727549974027173888) }, { argument := 14504163061694784847670983786496, coefficient := (-14504163061694784847670983786496) }, { argument := 3596231769727549974027173888, coefficient := (-3596231769727549974027173888) }, { argument := 3501594091576824974710669312, coefficient := (-3501594091576824974710669312) }, { argument := 132303474054713549044473397248, coefficient := (-132303474054713549044473397248) }, { argument := 3501594091576824974710669312, coefficient := (-3501594091576824974710669312) }, { argument := 40599563926661024706780463104, coefficient := (-40599563926661024706780463104) }, { argument := 132303474054713549044473397248, coefficient := (-132303474054713549044473397248) }, { argument := 374164127902385740155501674496, coefficient := (-374164127902385740155501674496) }, { argument := 3501594091576824974710669312, coefficient := (-3501594091576824974710669312) }, { argument := 3501594091576824974710669312, coefficient := (-3501594091576824974710669312) }, { argument := 3880144804179724971976687616, coefficient := (-3880144804179724971976687616) }, { argument := 6573534144154546137464832, coefficient := (-6573534144154546137464832) }, { argument := 95316245090240918993240064, coefficient := (-95316245090240918993240064) }, { argument := 168720709699966684194930688, coefficient := (-168720709699966684194930688) }, { argument := 5477945120128788447887360, coefficient := (-5477945120128788447887360) }, { argument := 105176546306472738199437312, coefficient := (-105176546306472738199437312) }, { argument := 5477945120128788447887360, coefficient := (-5477945120128788447887360) }, { argument := 167625120675940926505353216, coefficient := (-167625120675940926505353216) }, { argument := 175294243844121230332395520, coefficient := (-175294243844121230332395520) }, { argument := 105176546306472738199437312, coefficient := (-105176546306472738199437312) }, { argument := 2685288697887132097154383872, coefficient := (-2685288697887132097154383872) }, { argument := 172007476772043957263663104, coefficient := (-172007476772043957263663104) }, { argument := 95316245090240918993240064, coefficient := (-95316245090240918993240064) }, { argument := 167625120675940926505353216, coefficient := (-167625120675940926505353216) }, { argument := 5477945120128788447887360, coefficient := (-5477945120128788447887360) }, { argument := 172007476772043957263663104, coefficient := (-172007476772043957263663104) }, { argument := 5477945120128788447887360, coefficient := (-5477945120128788447887360) }, { argument := 167625120675940926505353216, coefficient := (-167625120675940926505353216) }, { argument := 175294243844121230332395520, coefficient := (-175294243844121230332395520) }, { argument := 6573534144154546137464832, coefficient := (-6573534144154546137464832) }, { argument := 3735002230457291369533669376, coefficient := (-3735002230457291369533669376) }, { argument := 149324696185447411089626103808, coefficient := (-149324696185447411089626103808) }, { argument := 149324659693175947273705619456, coefficient := (-149324659693175947273705619456) }, { argument := 3735002230457291369533669376, coefficient := (-3735002230457291369533669376) }, { argument := 85900724516030754052957536256, coefficient := (-85900724516030754052957536256) }, { argument := 126937211059536063344148480, coefficient := (-126937211059536063344148480) }, { argument := 6573534144154546137464832, coefficient := (-6573534144154546137464832) }, { argument := 314337170549107448462505410560, coefficient := (-314337170549107448462505410560) }, { argument := 176805401118639516800778240, coefficient := (-176805401118639516800778240) }, { argument := 85896847786105068025272074240, coefficient := (-85896847786105068025272074240) }, { argument := 177032074709817259771035648, coefficient := (-177032074709817259771035648) }, { argument := 177032074709817259771035648, coefficient := (-177032074709817259771035648) }, { argument := 126710537468358320373891072, coefficient := (-126710537468358320373891072) }, { argument := 6573534144154546137464832, coefficient := (-6573534144154546137464832) }, { argument := 141652201134743198223577382912, coefficient := (-141652201134743198223577382912) }, { argument := 9953342000462222015977402400768, coefficient := (-9953342000462222015977402400768) }, { argument := 68696008835008848434577801216, coefficient := (-68696008835008848434577801216) }, { argument := 88590094456100311457800912896, coefficient := (-88590094456100311457800912896) }, { argument := 1186033739456643848718797242368, coefficient := (-1186033739456643848718797242368) }, { argument := 2074874791823087298297351634944, coefficient := (-2074874791823087298297351634944) }, { argument := 9951563372860234269485090996224, coefficient := (-9951563372860234269485090996224) }, { argument := 1186033739456643848718797242368, coefficient := (-1186033739456643848718797242368) }, { argument := 66945484036069308541943414784, coefficient := (-66945484036069308541943414784) }, { argument := 68725023054679599534770749440, coefficient := (-68725023054679599534770749440) }, { argument := 68696008835008848434577801216, coefficient := (-68696008835008848434577801216) }, { argument := 66916469816398557441750466560, coefficient := (-66916469816398557441750466560) }, { argument := 2074874791823087298297351634944, coefficient := (-2074874791823087298297351634944) }, { argument := 66916469816398557441750466560, coefficient := (-66916469816398557441750466560) }, { argument := 141651289718120653723061452800, coefficient := (-141651289718120653723061452800) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15
