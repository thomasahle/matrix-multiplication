import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 12, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-5762655258350160584523929167593472)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    85771988393, 14207618117007, 7875, 2025, 7875, 6975,
    326475, 88875, 2025, 326475, 7875, 7875,
    3375, 7875, 88875, 3375, 7875, 6975,
    408460507, 42826347473, 461625220875, 21413190071, 408460507, 4265203965453,
    17955, 156462199366131, 282555, 8505, 1251656029567161, 8505,
    8505, 728595, 8505, 282555, 728595, 34163197085511,
    8505, 8505, 17955, 71590234486685, 43309394051, 381766234988643,
    39548421157, 1830840305, 39493607027, 38247273029, 71611796203421, 43309394051,
    912788107, 312214867368565, 16841095190726027, 24462240225, 229914990915, 2718175442575,
    190740792155, 4210273570772681, 2718175442575, 24462240225, 190808072155, 190793224155,
    190808072155, 190740792155, 190793224155, 78053943750967
  ]
def negativeCoefficients : Array ℕ := #[
    197776739822357149707598299136, 31992711828787516619133812736, 148754544210393824231424000, 153004674044976504923750400, 148754544210393824231424000, 131754024872063101462118400,
    6166938389979469684565606400, 1678801284660158873468928000, 153004674044976504923750400, 6166938389979469684565606400, 148754544210393824231424000, 148754544210393824231424000,
    127503895037480420769792000, 148754544210393824231424000, 1678801284660158873468928000, 127503895037480420769792000, 148754544210393824231424000, 131754024872063101462118400,
    1883691609211662205953507328, 197501667861547195396461166592, 2128870576862692261333303296000, 197501818520717731400796602368, 1883691609211662205953507328, 19208770989473292694415474688,
    169580180399848959623823360, 704643102762875827049491070976, 1334328261567232603355873280, 160654907747225330169937920, 704619703544337600422432735232, 160654907747225330169937920,
    160654907747225330169937920, 6881385215172818308945674240, 160654907747225330169937920, 1334328261567232603355873280, 6881385215172818308945674240, 19232170208011519321473810432,
    160654907747225330169937920, 160654907747225330169937920, 169580180399848959623823360, 80603438339400249495718461440, 199729327011558990064966959104, 859661136818744913517256638464,
    182384900900614799650799484928, 8443260636541834490512670720, 182132115343681538414669201408, 176384414270814230375580041216, 80627714674264678942537416704, 199729327011558990064966959104,
    8418984301677405043693715456, 703045380170299082512919429120, 37922775012732393730087579549696, 225624342450089079253814476800, 265073937257391353133835223040, 3133842921038951180364100403200,
    7037093154599823169251400744960, 37922772968919387540533964439552, 3133842921038951180364100403200, 225624342450089079253814476800, 219986729640074422703651553280, 219969611061574020239751905280,
    219986729640074422703651553280, 7037093154599823169251400744960, 219969611061574020239751905280, 703047423983305272066534539264
  ]
def negativeScales : Array ℕ := #[
    36, 43, 12, 10, 12, 12,
    18, 16, 10, 18, 12, 12,
    11, 12, 16, 11, 12, 12,
    28, 35, 38, 34, 28, 41,
    14, 47, 18, 13, 50, 13,
    13, 19, 13, 18, 19, 44,
    13, 13, 14, 46, 35, 48,
    35, 30, 35, 35, 46, 35,
    29, 48, 53, 34, 37, 41,
    37, 51, 41, 34, 37, 37,
    37, 37, 37, 46
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36319787514958093, 43691729943079975, 12943064217429565, 10983706210875052, 12943064217429565, 12767977501935366,
    18316612995283782, 16439490034281534, 10983706210875052, 18316612995283782, 12943064217429565, 12943064217429565,
    11720671786942400, 12943064217429565, 16439490034281534, 11720671786942400, 12943064217429565, 12767977501935366,
    28605621353732004, 35317779588341847, 38747931091696951, 34317780688864985, 28605621353732004, 41955751884151798,
    14132098032552021, 47152807478397666, 18108172193306541, 13054095520550748, 50152759569751531, 13054095520550748,
    13054095520550748, 19474757569023584, 13054095520550748, 18108172193306541, 19474757569023584, 44957508237989948,
    13054095520550748, 13054095520550748, 14132098032552021, 46024828038644047, 35333960936431892, 48439682838790542,
    35202901049780730, 30769858811915330, 35200900086798998, 35154637838436149, 46025262487539684, 35333960936431892,
    29765704753841541, 48149532567110450, 53902835483931817, 34509837479211242, 37742309579661806, 41305775715417500,
    37472822457659939, 51902835406179089, 41305775715417500, 34509837479211242, 37473331249756767, 37473218980033445,
    37473331249756767, 37472822457659939, 37473218980033445, 46149536761142139
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
noncomputable def negativeCeiling : ℝ := 31188657649 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 197776739822357149707598299136, coefficient := (-197776739822357149707598299136) }, { argument := 31992711828787516619133812736, coefficient := (-31992711828787516619133812736) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 153004674044976504923750400, coefficient := (-153004674044976504923750400) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 131754024872063101462118400, coefficient := (-131754024872063101462118400) }, { argument := 6166938389979469684565606400, coefficient := (-6166938389979469684565606400) }, { argument := 1678801284660158873468928000, coefficient := (-1678801284660158873468928000) }, { argument := 153004674044976504923750400, coefficient := (-153004674044976504923750400) }, { argument := 6166938389979469684565606400, coefficient := (-6166938389979469684565606400) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 127503895037480420769792000, coefficient := (-127503895037480420769792000) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 1678801284660158873468928000, coefficient := (-1678801284660158873468928000) }, { argument := 127503895037480420769792000, coefficient := (-127503895037480420769792000) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 131754024872063101462118400, coefficient := (-131754024872063101462118400) }, { argument := 1883691609211662205953507328, coefficient := (-1883691609211662205953507328) }, { argument := 197501667861547195396461166592, coefficient := (-197501667861547195396461166592) }, { argument := 2128870576862692261333303296000, coefficient := (-2128870576862692261333303296000) }, { argument := 197501818520717731400796602368, coefficient := (-197501818520717731400796602368) }, { argument := 1883691609211662205953507328, coefficient := (-1883691609211662205953507328) }, { argument := 19208770989473292694415474688, coefficient := (-19208770989473292694415474688) }, { argument := 169580180399848959623823360, coefficient := (-169580180399848959623823360) }, { argument := 704643102762875827049491070976, coefficient := (-704643102762875827049491070976) }, { argument := 1334328261567232603355873280, coefficient := (-1334328261567232603355873280) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 704619703544337600422432735232, coefficient := (-704619703544337600422432735232) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 6881385215172818308945674240, coefficient := (-6881385215172818308945674240) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 1334328261567232603355873280, coefficient := (-1334328261567232603355873280) }, { argument := 6881385215172818308945674240, coefficient := (-6881385215172818308945674240) }, { argument := 19232170208011519321473810432, coefficient := (-19232170208011519321473810432) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 160654907747225330169937920, coefficient := (-160654907747225330169937920) }, { argument := 169580180399848959623823360, coefficient := (-169580180399848959623823360) }, { argument := 80603438339400249495718461440, coefficient := (-80603438339400249495718461440) }, { argument := 199729327011558990064966959104, coefficient := (-199729327011558990064966959104) }, { argument := 859661136818744913517256638464, coefficient := (-859661136818744913517256638464) }, { argument := 182384900900614799650799484928, coefficient := (-182384900900614799650799484928) }, { argument := 8443260636541834490512670720, coefficient := (-8443260636541834490512670720) }, { argument := 182132115343681538414669201408, coefficient := (-182132115343681538414669201408) }, { argument := 176384414270814230375580041216, coefficient := (-176384414270814230375580041216) }, { argument := 80627714674264678942537416704, coefficient := (-80627714674264678942537416704) }, { argument := 199729327011558990064966959104, coefficient := (-199729327011558990064966959104) }, { argument := 8418984301677405043693715456, coefficient := (-8418984301677405043693715456) }, { argument := 703045380170299082512919429120, coefficient := (-703045380170299082512919429120) }, { argument := 37922775012732393730087579549696, coefficient := (-37922775012732393730087579549696) }, { argument := 225624342450089079253814476800, coefficient := (-225624342450089079253814476800) }, { argument := 265073937257391353133835223040, coefficient := (-265073937257391353133835223040) }, { argument := 3133842921038951180364100403200, coefficient := (-3133842921038951180364100403200) }, { argument := 7037093154599823169251400744960, coefficient := (-7037093154599823169251400744960) }, { argument := 37922772968919387540533964439552, coefficient := (-37922772968919387540533964439552) }, { argument := 3133842921038951180364100403200, coefficient := (-3133842921038951180364100403200) }, { argument := 225624342450089079253814476800, coefficient := (-225624342450089079253814476800) }, { argument := 219986729640074422703651553280, coefficient := (-219986729640074422703651553280) }, { argument := 219969611061574020239751905280, coefficient := (-219969611061574020239751905280) }, { argument := 219986729640074422703651553280, coefficient := (-219986729640074422703651553280) }, { argument := 7037093154599823169251400744960, coefficient := (-7037093154599823169251400744960) }, { argument := 219969611061574020239751905280, coefficient := (-219969611061574020239751905280) }, { argument := 703047423983305272066534539264, coefficient := (-703047423983305272066534539264) }] }

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

end TermShard2


end Parent2

namespace Parent2

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-31090114995375539760124947909836800)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    229914990915, 34350383868259, 4385551062271505, 924536305875, 174434018161484735, 30479218875,
    71118177375, 924536305875, 924536305875, 30479218875, 11409387598875, 457188283125,
    4385551062822929, 924536305875, 71118177375, 457188283125, 71118177375, 924536305875,
    924536305875, 142597075623981, 7875, 2025, 7875, 6975,
    326475, 88875, 2025, 326475, 7875, 7875,
    3375, 7875, 88875, 3375, 7875, 6975,
    13465731, 1411857609, 15218413875, 705929343, 13465731, 224500100620787,
    4617, 8387726592712205, 72657, 2187, 67098303581816647, 2187,
    2187, 187353, 2187, 72657, 187353, 1799509964847289,
    2187, 2187, 4617, 31420039, 3294334421, 35509632375,
    1647168467, 31420039, 87391855, 17955
  ]
def negativeCoefficients : Array ℕ := #[
    265073937257391353133835223040, 309400751978249458722094972928, 39501532259720465634191957032960, 2131835577666122194844909568000, 392790489596400492152475646689280, 1124484700307405113764347904000,
    81993676064081622878650368000, 2131835577666122194844909568000, 2131835577666122194844909568000, 1124484700307405113764347904000, 26308256634275332140778389504000, 2108408813076384588308152320000,
    39501532264687251476038253805568, 2131835577666122194844909568000, 81993676064081622878650368000, 2108408813076384588308152320000, 81993676064081622878650368000, 2131835577666122194844909568000,
    2131835577666122194844909568000, 321100068322141634992734732288, 148754544210393824231424000, 153004674044976504923750400, 148754544210393824231424000, 131754024872063101462118400,
    6166938389979469684565606400, 1678801284660158873468928000, 153004674044976504923750400, 6166938389979469684565606400, 148754544210393824231424000, 148754544210393824231424000,
    127503895037480420769792000, 148754544210393824231424000, 1678801284660158873468928000, 127503895037480420769792000, 148754544210393824231424000, 131754024872063101462118400,
    993595574089667976766685184, 104176703926969949220111384576, 1122920743839661852131852288000, 104176783395543418760859746304, 993595574089667976766685184, 1011058569500415190926048100352,
    174425328411273215613075456, 37774962357424286508041036103680, 1372451926183439249166041088, 165245047968574625317650432, 37772986876032733561929926180864, 165245047968574625317650432,
    165245047968574625317650432, 7077996221320613117772693504, 165245047968574625317650432, 1372451926183439249166041088, 7077996221320613117772693504, 1013034050891968137037158023168,
    165245047968574625317650432, 165245047968574625317650432, 174425328411273215613075456, 72449677277371623305904128, 7596217994674892130633121792, 81879637571642010051280896000,
    7596223789258374284646023168, 72449677277371623305904128, 6448380733246937787761950720, 169580180399848959623823360
  ]
def negativeScales : Array ℕ := #[
    37, 44, 51, 39, 57, 34,
    36, 39, 39, 34, 43, 38,
    51, 39, 36, 38, 36, 39,
    39, 47, 12, 10, 12, 12,
    18, 16, 10, 18, 12, 12,
    11, 12, 16, 11, 12, 12,
    23, 30, 33, 29, 23, 47,
    12, 52, 16, 11, 55, 11,
    11, 17, 11, 16, 17, 50,
    11, 11, 12, 24, 31, 35,
    30, 24, 26, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    37742309579661806, 44965391468387038, 51961679570531411, 39749939018322853, 57275459035350103, 34827106879732363,
    36049499299957180, 39749939018322853, 39749939018322853, 34827106879732363, 43375286590300180, 38733997474387123,
    51961679570712811, 39749939018322853, 36049499299957180, 38733997474387123, 36049499299957180, 39749939018322853,
    39749939018322853, 47018937723766997, 12943064217429565, 10983706210875052, 12943064217429565, 12767977501935366,
    18316612995283782, 16439490034281534, 10983706210875052, 18316612995283782, 12943064217429565, 12943064217429565,
    11720671786942400, 12943064217429565, 16439490034281534, 11720671786942400, 12943064217429565, 12767977501935366,
    23682789214295891, 30394947448864312, 33825098953073024, 29394948549387450, 23682789214295891, 47673709420043052,
    12172740017049367, 52897201263413615, 16148814177803887, 11094737505048094, 55897125814180397, 11094737505048094,
    11094737505048094, 17515399553521265, 11094737505048094, 16148814177803887, 17515399553521265, 50676525514609030,
    11094737505048094, 11094737505048094, 12172740017049367, 24905181640375697, 31617339870209827, 35047491373340934,
    30617340970732965, 24905181640375697, 26380995489719092, 14132098032552021
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
noncomputable def negativeCeiling : ℝ := 394803786623 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 265073937257391353133835223040, coefficient := (-265073937257391353133835223040) }, { argument := 309400751978249458722094972928, coefficient := (-309400751978249458722094972928) }, { argument := 39501532259720465634191957032960, coefficient := (-39501532259720465634191957032960) }, { argument := 2131835577666122194844909568000, coefficient := (-2131835577666122194844909568000) }, { argument := 392790489596400492152475646689280, coefficient := (-392790489596400492152475646689280) }, { argument := 1124484700307405113764347904000, coefficient := (-1124484700307405113764347904000) }, { argument := 81993676064081622878650368000, coefficient := (-81993676064081622878650368000) }, { argument := 2131835577666122194844909568000, coefficient := (-2131835577666122194844909568000) }, { argument := 2131835577666122194844909568000, coefficient := (-2131835577666122194844909568000) }, { argument := 1124484700307405113764347904000, coefficient := (-1124484700307405113764347904000) }, { argument := 26308256634275332140778389504000, coefficient := (-26308256634275332140778389504000) }, { argument := 2108408813076384588308152320000, coefficient := (-2108408813076384588308152320000) }, { argument := 39501532264687251476038253805568, coefficient := (-39501532264687251476038253805568) }, { argument := 2131835577666122194844909568000, coefficient := (-2131835577666122194844909568000) }, { argument := 81993676064081622878650368000, coefficient := (-81993676064081622878650368000) }, { argument := 2108408813076384588308152320000, coefficient := (-2108408813076384588308152320000) }, { argument := 81993676064081622878650368000, coefficient := (-81993676064081622878650368000) }, { argument := 2131835577666122194844909568000, coefficient := (-2131835577666122194844909568000) }, { argument := 2131835577666122194844909568000, coefficient := (-2131835577666122194844909568000) }, { argument := 321100068322141634992734732288, coefficient := (-321100068322141634992734732288) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 153004674044976504923750400, coefficient := (-153004674044976504923750400) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 131754024872063101462118400, coefficient := (-131754024872063101462118400) }, { argument := 6166938389979469684565606400, coefficient := (-6166938389979469684565606400) }, { argument := 1678801284660158873468928000, coefficient := (-1678801284660158873468928000) }, { argument := 153004674044976504923750400, coefficient := (-153004674044976504923750400) }, { argument := 6166938389979469684565606400, coefficient := (-6166938389979469684565606400) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 127503895037480420769792000, coefficient := (-127503895037480420769792000) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 1678801284660158873468928000, coefficient := (-1678801284660158873468928000) }, { argument := 127503895037480420769792000, coefficient := (-127503895037480420769792000) }, { argument := 148754544210393824231424000, coefficient := (-148754544210393824231424000) }, { argument := 131754024872063101462118400, coefficient := (-131754024872063101462118400) }, { argument := 993595574089667976766685184, coefficient := (-993595574089667976766685184) }, { argument := 104176703926969949220111384576, coefficient := (-104176703926969949220111384576) }, { argument := 1122920743839661852131852288000, coefficient := (-1122920743839661852131852288000) }, { argument := 104176783395543418760859746304, coefficient := (-104176783395543418760859746304) }, { argument := 993595574089667976766685184, coefficient := (-993595574089667976766685184) }, { argument := 1011058569500415190926048100352, coefficient := (-1011058569500415190926048100352) }, { argument := 174425328411273215613075456, coefficient := (-174425328411273215613075456) }, { argument := 37774962357424286508041036103680, coefficient := (-37774962357424286508041036103680) }, { argument := 1372451926183439249166041088, coefficient := (-1372451926183439249166041088) }, { argument := 165245047968574625317650432, coefficient := (-165245047968574625317650432) }, { argument := 37772986876032733561929926180864, coefficient := (-37772986876032733561929926180864) }, { argument := 165245047968574625317650432, coefficient := (-165245047968574625317650432) }, { argument := 165245047968574625317650432, coefficient := (-165245047968574625317650432) }, { argument := 7077996221320613117772693504, coefficient := (-7077996221320613117772693504) }, { argument := 165245047968574625317650432, coefficient := (-165245047968574625317650432) }, { argument := 1372451926183439249166041088, coefficient := (-1372451926183439249166041088) }, { argument := 7077996221320613117772693504, coefficient := (-7077996221320613117772693504) }, { argument := 1013034050891968137037158023168, coefficient := (-1013034050891968137037158023168) }, { argument := 165245047968574625317650432, coefficient := (-165245047968574625317650432) }, { argument := 165245047968574625317650432, coefficient := (-165245047968574625317650432) }, { argument := 174425328411273215613075456, coefficient := (-174425328411273215613075456) }, { argument := 72449677277371623305904128, coefficient := (-72449677277371623305904128) }, { argument := 7596217994674892130633121792, coefficient := (-7596217994674892130633121792) }, { argument := 81879637571642010051280896000, coefficient := (-81879637571642010051280896000) }, { argument := 7596223789258374284646023168, coefficient := (-7596223789258374284646023168) }, { argument := 72449677277371623305904128, coefficient := (-72449677277371623305904128) }, { argument := 6448380733246937787761950720, coefficient := (-6448380733246937787761950720) }, { argument := 169580180399848959623823360, coefficient := (-169580180399848959623823360) }] }

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

end TermShard3


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
