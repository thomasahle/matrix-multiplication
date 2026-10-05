import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 5, for level-four region 1, branch 1,
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

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-355313156479994938681766952566784)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3135, 9475500729, 3135, 6105, 115335, 6105,
    70785, 115335, 497803653, 6105, 6105, 6765,
    20657384717, 148499917233, 41325018165, 260046817, 260046879, 8241,
    238989, 211519, 13735, 8241, 13735, 420291,
    13735, 8241, 6732897, 431279, 238989, 420291,
    13735, 431279, 13735, 420291, 13735, 8241,
    13212638553, 207009, 124783858725, 2166021, 95931, 249567656541,
    95931, 186813, 3529251, 186813, 2166021, 3529251,
    13212638553, 186813, 186813, 207009, 40386488011, 36293147523,
    40396466985, 13246700889, 6765, 124791428133, 70785, 3135,
    249582795357, 3135, 6105, 115335
  ]
def negativeCoefficients : Array ℕ := #[
    59218475695185350979747840, 43698034229527821517917782016, 59218475695185350979747840, 57660094755838368059228160, 2178616553207082122886512640, 57660094755838368059228160,
    668545422979855672902942720, 2178616553207082122886512640, 1147857073231089506929606656, 57660094755838368059228160, 57660094755838368059228160, 63893618513226299741306880,
    47632686138332251631160131584, 171208748010262604141096337408, 47644502120697082466575319040, 9594034160763564560476012544, 9594036448159829700460412928, 77834044370657492412137472,
    1128593643374533639975993344, 1997740472180208971911528448, 64861703642214577010114560, 1245344709930519878594199552, 64861703642214577010114560, 1984768131451766056509505536,
    2075574516550866464323665920, 1245344709930519878594199552, 31795207125413585650358157312, 2036657494365537718117597184, 1128593643374533639975993344, 1984768131451766056509505536,
    64861703642214577010114560, 2036657494365537718117597184, 64861703642214577010114560, 1984768131451766056509505536, 2075574516550866464323665920, 77834044370657492412137472,
    30466270240702386925738131456, 1955144726504724772083990528, 1150927953215001837767019724800, 20457489943183583590830047232, 1812085356272671739980283904, 1150927672321818141373249880064,
    1812085356272671739980283904, 1764398899528654062612381696, 66665666528136712960327286784, 1764398899528654062612381696, 20457489943183583590830047232, 66665666528136712960327286784,
    30466270240702386925738131456, 1764398899528654062612381696, 1764398899528654062612381696, 1955144726504724772083990528, 46562450523428506664735604736, 167372600996541685663417761792,
    46573955497147019270931087360, 30544812640045474864932323328, 2044595792423241591721820160, 1150997768681084582601859006464, 21393453535355381532894167040, 1894991222245931231351930880,
    1150997487787900886208089161728, 1894991222245931231351930880, 1845123032186827777895301120, 69715729702626627932368404480
  ]
def negativeScales : Array ℕ := #[
    11, 33, 11, 12, 16, 12,
    16, 16, 28, 12, 12, 12,
    34, 37, 35, 27, 27, 13,
    17, 17, 13, 13, 13, 18,
    13, 13, 22, 18, 17, 18,
    13, 18, 13, 18, 13, 13,
    33, 17, 36, 21, 16, 37,
    16, 17, 21, 17, 21, 21,
    33, 17, 17, 17, 35, 35,
    35, 33, 12, 36, 16, 11,
    37, 11, 12, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11614249727697750, 33141555037919843, 11614249727697750, 12575775579877617, 16815470860503971, 12575775579877617,
    16111156051745362, 16815470860503971, 28891001580004972, 12575775579877617, 12575775579877617, 12723874218989575,
    34265938565388103, 37111671170695622, 35266296402548495, 27954196149591722, 27954196493557088, 13008603695797013,
    17866584693293866, 17690427735828455, 13745569290167282, 13008603695797013, 13745569290167282, 18681029037814535,
    13745569290167282, 13008603695797013, 22682795963990732, 18718261944078068, 17866584693293866, 18681029037814535,
    13745569290167282, 18718261944078068, 13745569290167282, 18681029037814535, 13745569290167282, 13008603695797013,
    33621199549246831, 17659333966696159, 36860640373962964, 21046615799550651, 16549709475496009, 37860640021861630,
    16549709475496009, 17511235327680448, 21750930607656040, 17511235327680448, 21046615799550651, 21750930607656040,
    33621199549246831, 17511235327680448, 17511235327680448, 17659333966696159, 35233153644322702, 35078978128835320,
    35233510071402571, 33624914047902148, 12723874218989575, 36860727885414607, 16111156051745362, 11614249727697750,
    37860727533334629, 11614249727697750, 12575775579877617, 16815470860503971
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
noncomputable def negativeCeiling : ℝ := 1220004871 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 59218475695185350979747840, coefficient := (-59218475695185350979747840) }, { argument := 43698034229527821517917782016, coefficient := (-43698034229527821517917782016) }, { argument := 59218475695185350979747840, coefficient := (-59218475695185350979747840) }, { argument := 57660094755838368059228160, coefficient := (-57660094755838368059228160) }, { argument := 2178616553207082122886512640, coefficient := (-2178616553207082122886512640) }, { argument := 57660094755838368059228160, coefficient := (-57660094755838368059228160) }, { argument := 668545422979855672902942720, coefficient := (-668545422979855672902942720) }, { argument := 2178616553207082122886512640, coefficient := (-2178616553207082122886512640) }, { argument := 1147857073231089506929606656, coefficient := (-1147857073231089506929606656) }, { argument := 57660094755838368059228160, coefficient := (-57660094755838368059228160) }, { argument := 57660094755838368059228160, coefficient := (-57660094755838368059228160) }, { argument := 63893618513226299741306880, coefficient := (-63893618513226299741306880) }, { argument := 47632686138332251631160131584, coefficient := (-47632686138332251631160131584) }, { argument := 171208748010262604141096337408, coefficient := (-171208748010262604141096337408) }, { argument := 47644502120697082466575319040, coefficient := (-47644502120697082466575319040) }, { argument := 9594034160763564560476012544, coefficient := (-9594034160763564560476012544) }, { argument := 9594036448159829700460412928, coefficient := (-9594036448159829700460412928) }, { argument := 77834044370657492412137472, coefficient := (-77834044370657492412137472) }, { argument := 1128593643374533639975993344, coefficient := (-1128593643374533639975993344) }, { argument := 1997740472180208971911528448, coefficient := (-1997740472180208971911528448) }, { argument := 64861703642214577010114560, coefficient := (-64861703642214577010114560) }, { argument := 1245344709930519878594199552, coefficient := (-1245344709930519878594199552) }, { argument := 64861703642214577010114560, coefficient := (-64861703642214577010114560) }, { argument := 1984768131451766056509505536, coefficient := (-1984768131451766056509505536) }, { argument := 2075574516550866464323665920, coefficient := (-2075574516550866464323665920) }, { argument := 1245344709930519878594199552, coefficient := (-1245344709930519878594199552) }, { argument := 31795207125413585650358157312, coefficient := (-31795207125413585650358157312) }, { argument := 2036657494365537718117597184, coefficient := (-2036657494365537718117597184) }, { argument := 1128593643374533639975993344, coefficient := (-1128593643374533639975993344) }, { argument := 1984768131451766056509505536, coefficient := (-1984768131451766056509505536) }, { argument := 64861703642214577010114560, coefficient := (-64861703642214577010114560) }, { argument := 2036657494365537718117597184, coefficient := (-2036657494365537718117597184) }, { argument := 64861703642214577010114560, coefficient := (-64861703642214577010114560) }, { argument := 1984768131451766056509505536, coefficient := (-1984768131451766056509505536) }, { argument := 2075574516550866464323665920, coefficient := (-2075574516550866464323665920) }, { argument := 77834044370657492412137472, coefficient := (-77834044370657492412137472) }, { argument := 30466270240702386925738131456, coefficient := (-30466270240702386925738131456) }, { argument := 1955144726504724772083990528, coefficient := (-1955144726504724772083990528) }, { argument := 1150927953215001837767019724800, coefficient := (-1150927953215001837767019724800) }, { argument := 20457489943183583590830047232, coefficient := (-20457489943183583590830047232) }, { argument := 1812085356272671739980283904, coefficient := (-1812085356272671739980283904) }, { argument := 1150927672321818141373249880064, coefficient := (-1150927672321818141373249880064) }, { argument := 1812085356272671739980283904, coefficient := (-1812085356272671739980283904) }, { argument := 1764398899528654062612381696, coefficient := (-1764398899528654062612381696) }, { argument := 66665666528136712960327286784, coefficient := (-66665666528136712960327286784) }, { argument := 1764398899528654062612381696, coefficient := (-1764398899528654062612381696) }, { argument := 20457489943183583590830047232, coefficient := (-20457489943183583590830047232) }, { argument := 66665666528136712960327286784, coefficient := (-66665666528136712960327286784) }, { argument := 30466270240702386925738131456, coefficient := (-30466270240702386925738131456) }, { argument := 1764398899528654062612381696, coefficient := (-1764398899528654062612381696) }, { argument := 1764398899528654062612381696, coefficient := (-1764398899528654062612381696) }, { argument := 1955144726504724772083990528, coefficient := (-1955144726504724772083990528) }, { argument := 46562450523428506664735604736, coefficient := (-46562450523428506664735604736) }, { argument := 167372600996541685663417761792, coefficient := (-167372600996541685663417761792) }, { argument := 46573955497147019270931087360, coefficient := (-46573955497147019270931087360) }, { argument := 30544812640045474864932323328, coefficient := (-30544812640045474864932323328) }, { argument := 2044595792423241591721820160, coefficient := (-2044595792423241591721820160) }, { argument := 1150997768681084582601859006464, coefficient := (-1150997768681084582601859006464) }, { argument := 21393453535355381532894167040, coefficient := (-21393453535355381532894167040) }, { argument := 1894991222245931231351930880, coefficient := (-1894991222245931231351930880) }, { argument := 1150997487787900886208089161728, coefficient := (-1150997487787900886208089161728) }, { argument := 1894991222245931231351930880, coefficient := (-1894991222245931231351930880) }, { argument := 1845123032186827777895301120, coefficient := (-1845123032186827777895301120) }, { argument := 69715729702626627932368404480, coefficient := (-69715729702626627932368404480) }] }

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


end Parent2

namespace Parent2

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 314794279987816933996086265143885824
def positiveArguments : Array ℕ := #[
    41373, 399, 11571, 10241, 665, 399,
    665, 20349, 665, 399, 325983, 20881,
    11571, 20349, 665, 20881
  ]
def positiveCoefficients : Array ℕ := #[
    3277906767702658439257693857251328, 15435564864839585302648455168, 223815690540173986888402599936, 396179498197549356101310349312, 12862970720699654418873712640, 246969037837433364842375282688,
    12862970720699654418873712640, 393606904053409425217535606784, 411615063062388941403958804480, 246969037837433364842375282688, 6305428247286970596131893936128, 403897280629969148752634576896,
    223815690540173986888402599936, 393606904053409425217535606784, 12862970720699654418873712640, 403897280629969148752634576896
  ]
def positiveScales : Array ℕ := #[
    15, 8, 13, 13, 9, 8,
    9, 14, 9, 8, 18, 14,
    13, 14, 9, 14
  ]
def negativeArguments : Array ℕ := #[
    6105, 70785, 115335, 13246700889, 6105, 6105,
    6765, 1254593052821, 1127472598713, 1254902400135, 10611587855, 10611590385,
    40386488011, 36293147523, 40396466985, 21265118745, 21265123815, 2049,
    7893061601083, 4059, 153629461830579, 42471, 1881, 307258945987371,
    1881, 3663, 69201, 3663, 42471, 69201,
    1973279684493, 3663, 3663, 4059, 430160306948257, 1561211909357981,
    215093735799521, 16624955342233, 16624953410151, 53321563167, 191659335909, 13333694655,
    101023994101, 101024018187, 1021, 260046817, 260046879, 2049
  ]
def negativeCoefficients : Array ℕ := #[
    1845123032186827777895301120, 21393453535355381532894167040, 69715729702626627932368404480, 30544812640045474864932323328, 1845123032186827777895301120, 1845123032186827777895301120,
    2044595792423241591721820160, 1446447310127684762999032119296, 5199549619644735045615382167552, 1446803963298387729737066741760, 195749245376869502725841223680, 195749292047132009211006812160,
    46562450523428506664735604736, 167372600996541685663417761792, 46573955497147019270931087360, 196136101593029323877473320960, 196136148355525550731186667520, 39633424070246002863567273984,
    8886797321362442336748961792, 76672342215871559689568256, 345942793526662711342207598592, 802254507575826807483531264, 71062170834222421175697408, 345942818663743848190788501504,
    71062170834222421175697408, 69192113707006041671073792, 2614339863848498547463815168, 69192113707006041671073792, 802254507575826807483531264, 2614339863848498547463815168,
    8886861651780444714096918528, 69192113707006041671073792, 69192113707006041671073792, 76672342215871559689568256, 121079362380109275411452526592, 439442085826936488040161345536,
    121087008549556336389680791552, 37436071342165837800783478784, 37436066991503950176162152448, 61475576834486672531486932992, 220968169928153375554544861184, 61490813214443493601176453120,
    232945470560636306455267377152, 232945526099171026376299905024, 39498024378449164396000182272, 9594034160763564560476012544, 9594036448159829700460412928, 39633424070246002863567273984
  ]
def negativeScales : Array ℕ := #[
    12, 16, 16, 33, 12, 12,
    12, 40, 40, 40, 33, 33,
    35, 35, 35, 34, 34, 11,
    42, 11, 47, 15, 10, 48,
    10, 11, 16, 11, 15, 16,
    40, 11, 11, 11, 48, 50,
    47, 43, 43, 35, 37, 33,
    36, 36, 9, 27, 27, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    15336401952259115, 8640244936221314, 13498225931349901, 13322068976196090, 9377210530388551, 8640244936221314,
    9377210530388551, 14312670278193841, 9377210530388551, 8640244936221314, 18314437204368028, 14349903184392816,
    13498225931349901, 14312670278193841, 9377210530388551, 14349903184392816
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    12575775579877617, 16111156051745362, 16815470860503971, 33624914047902148, 12575775579877617, 12575775579877617,
    12723874218989575, 40190356617657490, 40036229510327462, 40190712301775231, 33304921497599012, 33304921841564314,
    35233153644322702, 35078978128835320, 35233510071402571, 34307769859908042, 34307770203873344, 11000704269011247,
    42843722148908653, 11986908643884053, 47126448239540936, 15374190457579158, 10877284136413052, 48126448344370814,
    10877284136413052, 11838809987105390, 16078505265455047, 11838809987105390, 15374190457579158, 16078505265455047,
    40843732592360720, 11838809987105390, 11838809987105390, 11986908643884053, 48611867734617050, 50471587796520413,
    47611958838024239, 43918415704857526, 43918415537193582, 35634000023767400, 37479753318662248, 33634357543410234,
    36555907030396803, 36555907374362105, 9995767173005471, 27954196149591722, 27954196493557088, 11000704269011247
  ]

abbrev PositiveTerm := Fin 16
abbrev NegativeTerm := Fin 48
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
noncomputable def positiveFloor : ℝ := 607023964191 / 1000000000000
noncomputable def negativeCeiling : ℝ := 5597784003 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1845123032186827777895301120, coefficient := (-1845123032186827777895301120) }, { argument := 21393453535355381532894167040, coefficient := (-21393453535355381532894167040) }, { argument := 69715729702626627932368404480, coefficient := (-69715729702626627932368404480) }, { argument := 30544812640045474864932323328, coefficient := (-30544812640045474864932323328) }, { argument := 1845123032186827777895301120, coefficient := (-1845123032186827777895301120) }, { argument := 1845123032186827777895301120, coefficient := (-1845123032186827777895301120) }, { argument := 2044595792423241591721820160, coefficient := (-2044595792423241591721820160) }, { argument := 1446447310127684762999032119296, coefficient := (-1446447310127684762999032119296) }, { argument := 5199549619644735045615382167552, coefficient := (-5199549619644735045615382167552) }, { argument := 1446803963298387729737066741760, coefficient := (-1446803963298387729737066741760) }, { argument := 195749245376869502725841223680, coefficient := (-195749245376869502725841223680) }, { argument := 195749292047132009211006812160, coefficient := (-195749292047132009211006812160) }, { argument := 46562450523428506664735604736, coefficient := (-46562450523428506664735604736) }, { argument := 167372600996541685663417761792, coefficient := (-167372600996541685663417761792) }, { argument := 46573955497147019270931087360, coefficient := (-46573955497147019270931087360) }, { argument := 196136101593029323877473320960, coefficient := (-196136101593029323877473320960) }, { argument := 196136148355525550731186667520, coefficient := (-196136148355525550731186667520) }, { argument := 39633424070246002863567273984, coefficient := (-39633424070246002863567273984) }, { argument := 8886797321362442336748961792, coefficient := (-8886797321362442336748961792) }, { argument := 76672342215871559689568256, coefficient := (-76672342215871559689568256) }, { argument := 345942793526662711342207598592, coefficient := (-345942793526662711342207598592) }, { argument := 802254507575826807483531264, coefficient := (-802254507575826807483531264) }, { argument := 71062170834222421175697408, coefficient := (-71062170834222421175697408) }, { argument := 345942818663743848190788501504, coefficient := (-345942818663743848190788501504) }, { argument := 71062170834222421175697408, coefficient := (-71062170834222421175697408) }, { argument := 69192113707006041671073792, coefficient := (-69192113707006041671073792) }, { argument := 2614339863848498547463815168, coefficient := (-2614339863848498547463815168) }, { argument := 69192113707006041671073792, coefficient := (-69192113707006041671073792) }, { argument := 802254507575826807483531264, coefficient := (-802254507575826807483531264) }, { argument := 2614339863848498547463815168, coefficient := (-2614339863848498547463815168) }, { argument := 8886861651780444714096918528, coefficient := (-8886861651780444714096918528) }, { argument := 69192113707006041671073792, coefficient := (-69192113707006041671073792) }, { argument := 69192113707006041671073792, coefficient := (-69192113707006041671073792) }, { argument := 76672342215871559689568256, coefficient := (-76672342215871559689568256) }, { argument := 121079362380109275411452526592, coefficient := (-121079362380109275411452526592) }, { argument := 439442085826936488040161345536, coefficient := (-439442085826936488040161345536) }, { argument := 121087008549556336389680791552, coefficient := (-121087008549556336389680791552) }, { argument := 37436071342165837800783478784, coefficient := (-37436071342165837800783478784) }, { argument := 37436066991503950176162152448, coefficient := (-37436066991503950176162152448) }, { argument := 61475576834486672531486932992, coefficient := (-61475576834486672531486932992) }, { argument := 220968169928153375554544861184, coefficient := (-220968169928153375554544861184) }, { argument := 61490813214443493601176453120, coefficient := (-61490813214443493601176453120) }, { argument := 232945470560636306455267377152, coefficient := (-232945470560636306455267377152) }, { argument := 232945526099171026376299905024, coefficient := (-232945526099171026376299905024) }, { argument := 39498024378449164396000182272, coefficient := (-39498024378449164396000182272) }, { argument := 9594034160763564560476012544, coefficient := (-9594034160763564560476012544) }, { argument := 9594036448159829700460412928, coefficient := (-9594036448159829700460412928) }, { argument := 39633424070246002863567273984, coefficient := (-39633424070246002863567273984) }, { argument := 3277906767702658439257693857251328, coefficient := 3277906767702658439257693857251328 }, { argument := 15435564864839585302648455168, coefficient := 15435564864839585302648455168 }, { argument := 223815690540173986888402599936, coefficient := 223815690540173986888402599936 }, { argument := 396179498197549356101310349312, coefficient := 396179498197549356101310349312 }, { argument := 12862970720699654418873712640, coefficient := 12862970720699654418873712640 }, { argument := 246969037837433364842375282688, coefficient := 246969037837433364842375282688 }, { argument := 12862970720699654418873712640, coefficient := 12862970720699654418873712640 }, { argument := 393606904053409425217535606784, coefficient := 393606904053409425217535606784 }, { argument := 411615063062388941403958804480, coefficient := 411615063062388941403958804480 }, { argument := 246969037837433364842375282688, coefficient := 246969037837433364842375282688 }, { argument := 6305428247286970596131893936128, coefficient := 6305428247286970596131893936128 }, { argument := 403897280629969148752634576896, coefficient := 403897280629969148752634576896 }, { argument := 223815690540173986888402599936, coefficient := 223815690540173986888402599936 }, { argument := 393606904053409425217535606784, coefficient := 393606904053409425217535606784 }, { argument := 12862970720699654418873712640, coefficient := 12862970720699654418873712640 }, { argument := 403897280629969148752634576896, coefficient := 403897280629969148752634576896 }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
