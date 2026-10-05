import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 13, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13

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
def constantNumerator : ℤ := (-2530281505590765018368939275583488)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    513, 2049, 1021, 2049, 132474507425855, 101023994101,
    5071212164791033, 84917868661, 260046817, 10611587855, 21265118745, 16624955342233,
    101023994101, 260046817, 53678357858475, 5024773173485397, 20598136907, 53169625369,
    44492898337, 1251153435251, 20097205171829417, 44492898337, 40440214061, 20681243595,
    20598136907, 40274000685, 1251153435251, 40274000685, 214712138177879, 53169625369,
    7867906377407, 323503666208381, 12905431133, 13050108558508967, 4080370523, 485890233,
    12900491357, 25716409127, 4080370523, 396703664725, 25379309569, 1294016891043047,
    12900491357, 485890233, 25379309569, 485890233, 12900491357, 12935069789,
    7867906377407, 8241, 238989, 211519, 13735, 8241,
    13735, 420291, 13735, 8241, 6732897, 431279,
    238989, 420291, 13735, 431279
  ]
def negativeCoefficients : Array ℕ := #[
    39691452509587505063953170432, 39633424070246002863567273984, 39498024378449164396000182272, 39633424070246002863567273984, 37288258892448161453708410880, 232945470560636306455267377152,
    1427419325979351410871944347648, 195807273809293475898586038272, 9594034160763564560476012544, 195749245376869502725841223680, 196136101593029323877473320960, 37436071342165837800783478784,
    232945470560636306455267377152, 9594034160763564560476012544, 120872916224644072830979276800, 11314783295865049290415282323456, 47496069989832530442493886464, 61300404479809861346230534144,
    820749108720216314516542062592, 1442481701063608216198081150976, 11313720715379920929521196335104, 820749108720216314516542062592, 46624392441831089355710529536, 47687700965376234031090237440,
    47496069989832530442493886464, 46432761466287385767114178560, 1442481701063608216198081150976, 46432761466287385767114178560, 120872188186227289049685557248, 61300404479809861346230534144,
    8858475057369028567098195968, 1456930990589053990189427326976, 29757898158916811778074607616, 14693116010311376119462161809408, 18817387690922348419368353792, 1120386597008262901127970816,
    29746507810960130193819172864, 29649001103786092120298749952, 18817387690922348419368353792, 457368186017797165706484121600, 29260351774174429040915513344, 1456933497078148548051838435328,
    29746507810960130193819172864, 1120386597008262901127970816, 29260351774174429040915513344, 1120386597008262901127970816, 29746507810960130193819172864, 29826240246656901283607216128,
    8858475057369028567098195968, 77834044370657492412137472, 1128593643374533639975993344, 1997740472180208971911528448, 64861703642214577010114560, 1245344709930519878594199552,
    64861703642214577010114560, 1984768131451766056509505536, 2075574516550866464323665920, 1245344709930519878594199552, 31795207125413585650358157312, 2036657494365537718117597184,
    1128593643374533639975993344, 1984768131451766056509505536, 64861703642214577010114560, 2036657494365537718117597184
  ]
def negativeScales : Array ℕ := #[
    9, 11, 9, 11, 46, 36,
    52, 36, 27, 33, 34, 43,
    36, 27, 45, 52, 34, 35,
    35, 40, 54, 35, 35, 34,
    34, 35, 40, 35, 47, 35,
    42, 48, 33, 53, 31, 28,
    33, 34, 31, 38, 34, 50,
    33, 28, 34, 28, 33, 33,
    42, 13, 17, 17, 13, 13,
    13, 18, 13, 13, 22, 18,
    17, 18, 13, 18
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    9002815015607055, 11000704269011247, 9995767173005471, 11000704269011247, 46912708096980206, 36555907030396803,
    52171252057148793, 36305349110616287, 27954196149591722, 33304921497599012, 34307769859908042, 43918415704857526,
    36555907030396803, 27954196149591722, 45609405770474713, 52157979895448020, 34261794801010917, 35629883250172755,
    35372856029860281, 40186395863964949, 54157844404423355, 35372856029860281, 35235071582710145, 34267603888607538,
    34261794801010917, 35229129740792902, 40186395863964949, 35229129740792902, 47609397080847543, 35629883250172755,
    42839116930708300, 48200775390534764, 33587259287368857, 53534911326232960, 31926053024723458, 28856055193818461,
    33586706965286289, 34581970157003975, 31926053024723458, 38529270768837930, 34562933770815492, 50200777872530342,
    33586706965286289, 28856055193818461, 34562933770815492, 28856055193818461, 33586706965286289, 33590568786740794,
    42839116930708300, 13008603695797013, 17866584693293866, 17690427735828455, 13745569290167282, 13008603695797013,
    13745569290167282, 18681029037814535, 13745569290167282, 13008603695797013, 22682795963990732, 18718261944078068,
    17866584693293866, 18681029037814535, 13745569290167282, 18718261944078068
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
noncomputable def negativeCeiling : ℝ := 5966608827 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 39691452509587505063953170432, coefficient := (-39691452509587505063953170432) }, { argument := 39633424070246002863567273984, coefficient := (-39633424070246002863567273984) }, { argument := 39498024378449164396000182272, coefficient := (-39498024378449164396000182272) }, { argument := 39633424070246002863567273984, coefficient := (-39633424070246002863567273984) }, { argument := 37288258892448161453708410880, coefficient := (-37288258892448161453708410880) }, { argument := 232945470560636306455267377152, coefficient := (-232945470560636306455267377152) }, { argument := 1427419325979351410871944347648, coefficient := (-1427419325979351410871944347648) }, { argument := 195807273809293475898586038272, coefficient := (-195807273809293475898586038272) }, { argument := 9594034160763564560476012544, coefficient := (-9594034160763564560476012544) }, { argument := 195749245376869502725841223680, coefficient := (-195749245376869502725841223680) }, { argument := 196136101593029323877473320960, coefficient := (-196136101593029323877473320960) }, { argument := 37436071342165837800783478784, coefficient := (-37436071342165837800783478784) }, { argument := 232945470560636306455267377152, coefficient := (-232945470560636306455267377152) }, { argument := 9594034160763564560476012544, coefficient := (-9594034160763564560476012544) }, { argument := 120872916224644072830979276800, coefficient := (-120872916224644072830979276800) }, { argument := 11314783295865049290415282323456, coefficient := (-11314783295865049290415282323456) }, { argument := 47496069989832530442493886464, coefficient := (-47496069989832530442493886464) }, { argument := 61300404479809861346230534144, coefficient := (-61300404479809861346230534144) }, { argument := 820749108720216314516542062592, coefficient := (-820749108720216314516542062592) }, { argument := 1442481701063608216198081150976, coefficient := (-1442481701063608216198081150976) }, { argument := 11313720715379920929521196335104, coefficient := (-11313720715379920929521196335104) }, { argument := 820749108720216314516542062592, coefficient := (-820749108720216314516542062592) }, { argument := 46624392441831089355710529536, coefficient := (-46624392441831089355710529536) }, { argument := 47687700965376234031090237440, coefficient := (-47687700965376234031090237440) }, { argument := 47496069989832530442493886464, coefficient := (-47496069989832530442493886464) }, { argument := 46432761466287385767114178560, coefficient := (-46432761466287385767114178560) }, { argument := 1442481701063608216198081150976, coefficient := (-1442481701063608216198081150976) }, { argument := 46432761466287385767114178560, coefficient := (-46432761466287385767114178560) }, { argument := 120872188186227289049685557248, coefficient := (-120872188186227289049685557248) }, { argument := 61300404479809861346230534144, coefficient := (-61300404479809861346230534144) }, { argument := 8858475057369028567098195968, coefficient := (-8858475057369028567098195968) }, { argument := 1456930990589053990189427326976, coefficient := (-1456930990589053990189427326976) }, { argument := 29757898158916811778074607616, coefficient := (-29757898158916811778074607616) }, { argument := 14693116010311376119462161809408, coefficient := (-14693116010311376119462161809408) }, { argument := 18817387690922348419368353792, coefficient := (-18817387690922348419368353792) }, { argument := 1120386597008262901127970816, coefficient := (-1120386597008262901127970816) }, { argument := 29746507810960130193819172864, coefficient := (-29746507810960130193819172864) }, { argument := 29649001103786092120298749952, coefficient := (-29649001103786092120298749952) }, { argument := 18817387690922348419368353792, coefficient := (-18817387690922348419368353792) }, { argument := 457368186017797165706484121600, coefficient := (-457368186017797165706484121600) }, { argument := 29260351774174429040915513344, coefficient := (-29260351774174429040915513344) }, { argument := 1456933497078148548051838435328, coefficient := (-1456933497078148548051838435328) }, { argument := 29746507810960130193819172864, coefficient := (-29746507810960130193819172864) }, { argument := 1120386597008262901127970816, coefficient := (-1120386597008262901127970816) }, { argument := 29260351774174429040915513344, coefficient := (-29260351774174429040915513344) }, { argument := 1120386597008262901127970816, coefficient := (-1120386597008262901127970816) }, { argument := 29746507810960130193819172864, coefficient := (-29746507810960130193819172864) }, { argument := 29826240246656901283607216128, coefficient := (-29826240246656901283607216128) }, { argument := 8858475057369028567098195968, coefficient := (-8858475057369028567098195968) }, { argument := 77834044370657492412137472, coefficient := (-77834044370657492412137472) }, { argument := 1128593643374533639975993344, coefficient := (-1128593643374533639975993344) }, { argument := 1997740472180208971911528448, coefficient := (-1997740472180208971911528448) }, { argument := 64861703642214577010114560, coefficient := (-64861703642214577010114560) }, { argument := 1245344709930519878594199552, coefficient := (-1245344709930519878594199552) }, { argument := 64861703642214577010114560, coefficient := (-64861703642214577010114560) }, { argument := 1984768131451766056509505536, coefficient := (-1984768131451766056509505536) }, { argument := 2075574516550866464323665920, coefficient := (-2075574516550866464323665920) }, { argument := 1245344709930519878594199552, coefficient := (-1245344709930519878594199552) }, { argument := 31795207125413585650358157312, coefficient := (-31795207125413585650358157312) }, { argument := 2036657494365537718117597184, coefficient := (-2036657494365537718117597184) }, { argument := 1128593643374533639975993344, coefficient := (-1128593643374533639975993344) }, { argument := 1984768131451766056509505536, coefficient := (-1984768131451766056509505536) }, { argument := 64861703642214577010114560, coefficient := (-64861703642214577010114560) }, { argument := 2036657494365537718117597184, coefficient := (-2036657494365537718117597184) }] }

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
def constantNumerator : ℤ := (-40309052368532721771885256530460672)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    13735, 420291, 13735, 8241, 7893061601083, 4059,
    153629461830579, 42471, 1881, 307258945987371, 1881, 3663,
    69201, 3663, 42471, 69201, 1973279684493, 3663,
    3663, 4059, 132474492094401, 101024018187, 5071211253351687, 84917888907,
    260046879, 10611590385, 21265123815, 16624953410151, 101024018187, 260046879,
    389655158090455, 36783078769116457, 74041331717, 191124436307, 319870319051, 4497796602521,
    73559392082300685, 319870319051, 145383969791, 74344880417, 74041331717, 144776872391,
    4497796602521, 144776872391, 779305512057075, 191124436307, 153109513750351, 50591865805714909,
    121554819545, 2041716998202566739, 38465909119, 4615074821, 121553721817, 241586283099,
    38465909119, 3728390168177, 238506639277, 202367811714648905, 121553721817, 4615074821,
    238506639277, 4615074821, 121553721817, 121561405913
  ]
def negativeCoefficients : Array ℕ := #[
    64861703642214577010114560, 1984768131451766056509505536, 2075574516550866464323665920, 77834044370657492412137472, 8886797321362442336748961792, 76672342215871559689568256,
    345942793526662711342207598592, 802254507575826807483531264, 71062170834222421175697408, 345942818663743848190788501504, 71062170834222421175697408, 69192113707006041671073792,
    2614339863848498547463815168, 69192113707006041671073792, 802254507575826807483531264, 2614339863848498547463815168, 8886861651780444714096918528, 69192113707006041671073792,
    69192113707006041671073792, 76672342215871559689568256, 37288254577027503863214637056, 232945526099171026376299905024, 1427419069431982722346408476672, 195807320493391040439033790464,
    9594036448159829700460412928, 195749292047132009211006812160, 196136148355525550731186667520, 37436066991503950176162152448, 232945526099171026376299905024, 9594036448159829700460412928,
    438712706194791211928041553920, 41414064959533119604101027463168, 170727687132516601238948675584, 220351472674201931940607557632, 2950282956154808868258036318208, 5185606426394075778486942826496,
    41410256346431197349596071198720, 2950282956154808868258036318208, 167616305197156108090543702016, 171427622780367506060276137984, 170727687132516601238948675584, 166916369549305203269216239616,
    5185606426394075778486942826496, 166916369549305203269216239616, 438710001713502068463265382400, 220351472674201931940607557632, 344771974536479298562763522048, 56961376997648950638573273481216,
    1121145323536281362712871567360, 574692244518817951073066532470784, 709570781080763449663295586304, 42566552052003959865100730368, 1121135198782542090193533403136, 1114120084011499064950832234496,
    709570781080763449663295586304, 17194164809824008308457375531008, 1099917733655845381636681105408, 56961475089367218985186812231680, 1121135198782542090193533403136, 42566552052003959865100730368,
    1099917733655845381636681105408, 42566552052003959865100730368, 1121135198782542090193533403136, 1121206072058716997828900552704
  ]
def negativeScales : Array ℕ := #[
    13, 18, 13, 13, 42, 11,
    47, 15, 10, 48, 10, 11,
    16, 11, 15, 16, 40, 11,
    11, 11, 46, 36, 52, 36,
    27, 33, 34, 43, 36, 27,
    48, 55, 36, 37, 38, 42,
    56, 38, 37, 36, 36, 37,
    42, 37, 49, 37, 47, 55,
    36, 60, 35, 32, 36, 37,
    35, 41, 37, 57, 36, 32,
    37, 32, 36, 36
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    13745569290167282, 18681029037814535, 13745569290167282, 13008603695797013, 42843722148908653, 11986908643884053,
    47126448239540936, 15374190457579158, 10877284136413052, 48126448344370814, 10877284136413052, 11838809987105390,
    16078505265455047, 11838809987105390, 15374190457579158, 16078505265455047, 40843732592360720, 11838809987105390,
    11838809987105390, 11986908643884053, 46912707930015131, 36555907374362105, 52171251797855926, 36305349454581589,
    27954196493557088, 33304921841564314, 34307770203873344, 43918415537193582, 36555907374362105, 27954196493557088,
    48469191242678741, 55029891757573626, 36107611792815683, 37475721290339755, 38218696173930917, 42032355560286732,
    56029759075116298, 38218696173930917, 37081077248520758, 36113514346816291, 36107611792815683, 37075040199001656,
    42032355560286732, 37075040199001656, 49469182349036694, 37475721290339755, 47121557258641667, 55489754964281611,
    36822816140911934, 60824488617563007, 35162861354864896, 32103706891458750, 36822803112272422, 37813747587576299,
    35162861354864896, 41761689981827323, 37795238471243201, 57489757448707394, 36822803112272422, 32103706891458750,
    37795238471243201, 32103706891458750, 36822803112272422, 36822894310278274
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
noncomputable def negativeCeiling : ℝ := 577992651523 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 64861703642214577010114560, coefficient := (-64861703642214577010114560) }, { argument := 1984768131451766056509505536, coefficient := (-1984768131451766056509505536) }, { argument := 2075574516550866464323665920, coefficient := (-2075574516550866464323665920) }, { argument := 77834044370657492412137472, coefficient := (-77834044370657492412137472) }, { argument := 8886797321362442336748961792, coefficient := (-8886797321362442336748961792) }, { argument := 76672342215871559689568256, coefficient := (-76672342215871559689568256) }, { argument := 345942793526662711342207598592, coefficient := (-345942793526662711342207598592) }, { argument := 802254507575826807483531264, coefficient := (-802254507575826807483531264) }, { argument := 71062170834222421175697408, coefficient := (-71062170834222421175697408) }, { argument := 345942818663743848190788501504, coefficient := (-345942818663743848190788501504) }, { argument := 71062170834222421175697408, coefficient := (-71062170834222421175697408) }, { argument := 69192113707006041671073792, coefficient := (-69192113707006041671073792) }, { argument := 2614339863848498547463815168, coefficient := (-2614339863848498547463815168) }, { argument := 69192113707006041671073792, coefficient := (-69192113707006041671073792) }, { argument := 802254507575826807483531264, coefficient := (-802254507575826807483531264) }, { argument := 2614339863848498547463815168, coefficient := (-2614339863848498547463815168) }, { argument := 8886861651780444714096918528, coefficient := (-8886861651780444714096918528) }, { argument := 69192113707006041671073792, coefficient := (-69192113707006041671073792) }, { argument := 69192113707006041671073792, coefficient := (-69192113707006041671073792) }, { argument := 76672342215871559689568256, coefficient := (-76672342215871559689568256) }, { argument := 37288254577027503863214637056, coefficient := (-37288254577027503863214637056) }, { argument := 232945526099171026376299905024, coefficient := (-232945526099171026376299905024) }, { argument := 1427419069431982722346408476672, coefficient := (-1427419069431982722346408476672) }, { argument := 195807320493391040439033790464, coefficient := (-195807320493391040439033790464) }, { argument := 9594036448159829700460412928, coefficient := (-9594036448159829700460412928) }, { argument := 195749292047132009211006812160, coefficient := (-195749292047132009211006812160) }, { argument := 196136148355525550731186667520, coefficient := (-196136148355525550731186667520) }, { argument := 37436066991503950176162152448, coefficient := (-37436066991503950176162152448) }, { argument := 232945526099171026376299905024, coefficient := (-232945526099171026376299905024) }, { argument := 9594036448159829700460412928, coefficient := (-9594036448159829700460412928) }, { argument := 438712706194791211928041553920, coefficient := (-438712706194791211928041553920) }, { argument := 41414064959533119604101027463168, coefficient := (-41414064959533119604101027463168) }, { argument := 170727687132516601238948675584, coefficient := (-170727687132516601238948675584) }, { argument := 220351472674201931940607557632, coefficient := (-220351472674201931940607557632) }, { argument := 2950282956154808868258036318208, coefficient := (-2950282956154808868258036318208) }, { argument := 5185606426394075778486942826496, coefficient := (-5185606426394075778486942826496) }, { argument := 41410256346431197349596071198720, coefficient := (-41410256346431197349596071198720) }, { argument := 2950282956154808868258036318208, coefficient := (-2950282956154808868258036318208) }, { argument := 167616305197156108090543702016, coefficient := (-167616305197156108090543702016) }, { argument := 171427622780367506060276137984, coefficient := (-171427622780367506060276137984) }, { argument := 170727687132516601238948675584, coefficient := (-170727687132516601238948675584) }, { argument := 166916369549305203269216239616, coefficient := (-166916369549305203269216239616) }, { argument := 5185606426394075778486942826496, coefficient := (-5185606426394075778486942826496) }, { argument := 166916369549305203269216239616, coefficient := (-166916369549305203269216239616) }, { argument := 438710001713502068463265382400, coefficient := (-438710001713502068463265382400) }, { argument := 220351472674201931940607557632, coefficient := (-220351472674201931940607557632) }, { argument := 344771974536479298562763522048, coefficient := (-344771974536479298562763522048) }, { argument := 56961376997648950638573273481216, coefficient := (-56961376997648950638573273481216) }, { argument := 1121145323536281362712871567360, coefficient := (-1121145323536281362712871567360) }, { argument := 574692244518817951073066532470784, coefficient := (-574692244518817951073066532470784) }, { argument := 709570781080763449663295586304, coefficient := (-709570781080763449663295586304) }, { argument := 42566552052003959865100730368, coefficient := (-42566552052003959865100730368) }, { argument := 1121135198782542090193533403136, coefficient := (-1121135198782542090193533403136) }, { argument := 1114120084011499064950832234496, coefficient := (-1114120084011499064950832234496) }, { argument := 709570781080763449663295586304, coefficient := (-709570781080763449663295586304) }, { argument := 17194164809824008308457375531008, coefficient := (-17194164809824008308457375531008) }, { argument := 1099917733655845381636681105408, coefficient := (-1099917733655845381636681105408) }, { argument := 56961475089367218985186812231680, coefficient := (-56961475089367218985186812231680) }, { argument := 1121135198782542090193533403136, coefficient := (-1121135198782542090193533403136) }, { argument := 42566552052003959865100730368, coefficient := (-42566552052003959865100730368) }, { argument := 1099917733655845381636681105408, coefficient := (-1099917733655845381636681105408) }, { argument := 42566552052003959865100730368, coefficient := (-42566552052003959865100730368) }, { argument := 1121135198782542090193533403136, coefficient := (-1121135198782542090193533403136) }, { argument := 1121206072058716997828900552704, coefficient := (-1121206072058716997828900552704) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
