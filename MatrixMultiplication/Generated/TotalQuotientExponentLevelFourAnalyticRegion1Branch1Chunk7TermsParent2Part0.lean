import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 7, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7

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
def constantNumerator : ℤ := (-5049242812565691846332619748802560)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    93, 285, 843, 1881, 93, 939,
    1911, 93, 285, 93, 186528385937621, 4009827089051435,
    32045093149, 2598213579, 556882984267, 1007160220691, 4009818922741547, 556882984267,
    16453558363, 16454559835, 32045093149, 32043090205, 1007160220691, 32043090205,
    186528348188885, 2598213579, 111976178136205, 2162418234840361, 217359491811, 39605160007991615,
    8468551629, 14114252715, 431896133079, 14114252715, 8468551629, 6918806680893,
    443187535251, 2162419252040689, 431896133079, 14114252715, 443187535251, 14114252715,
    431896133079, 14114252715, 111976178136205, 1605, 4815, 10165,
    26215, 21935, 613645, 18725, 21935, 19795,
    10165, 10165, 19795, 613645, 19795, 1605,
    26215, 11201859, 5295951261, 201030087159
  ]
def negativeCoefficients : Array ℕ := #[
    1798881619586568211962789888, 44101613899541672293281300480, 32611982909924236616873803776, 36383831467121879641957072896, 1798881619586568211962789888, 36325803027780377441571176448,
    36964115860536901645816037376, 1798881619586568211962789888, 44101613899541672293281300480, 1798881619586568211962789888, 105006146175336250217963978752, 2257331973009020418374993182720,
    73890954017223287938217934848, 95857161881299867821385187328, 1284084736222121465112569053184, 2322353354038463547075651960832, 2257327375785249344775377649664, 1284084736222121465112569053184,
    75878645056026120356104241152, 75883263530446366869123235840, 73890954017223287938217934848, 73886335542803041425198940160, 2322353354038463547075651960832, 73886335542803041425198940160,
    105006124924687077304560517120, 95857161881299867821385187328, 63036984266073139911285800960, 4869332978323107755240380694528, 1002393729357271016217608454144, 44591445963484976923862116597760,
    624868818300636477642145529856, 32545250953158149877195079680, 995884679166639386242169438208, 1041448030501060796070242549760, 624868818300636477642145529856, 15953682017238125069801028059136,
    1021920879929165906143925501952, 4869335268854616826213535055872, 995884679166639386242169438208, 32545250953158149877195079680, 1021920879929165906143925501952, 32545250953158149877195079680,
    995884679166639386242169438208, 1041448030501060796070242549760, 63036984266073139911285800960, 242540742560184978175426560, 181905556920138733631569920, 192011421193479774388879360,
    247593674696855498554081280, 3314723481655861368397496320, 5795713160761086874316963840, 176852624783468213252915200, 3314723481655861368397496320, 186958489056809254010224640,
    192011421193479774388879360, 192011421193479774388879360, 186958489056809254010224640, 5795713160761086874316963840, 186958489056809254010224640, 242540742560184978175426560,
    247593674696855498554081280, 206637826122780004155654144, 24423264384626594207124946944, 231771910558599867613455581184
  ]
def negativeScales : Array ℕ := #[
    6, 8, 9, 10, 6, 9,
    10, 6, 8, 6, 47, 51,
    34, 31, 39, 39, 51, 39,
    33, 33, 34, 34, 39, 34,
    47, 31, 46, 50, 37, 55,
    32, 33, 38, 33, 32, 42,
    38, 50, 38, 33, 38, 33,
    38, 33, 46, 10, 12, 13,
    14, 14, 19, 14, 14, 14,
    13, 13, 14, 19, 14, 10,
    14, 23, 32, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    6539158811108986, 8154818109052105, 9719388821055554, 10877284136413052, 6539158811108986, 9874981350423323,
    10900112067353854, 6539158811108986, 8154818109052105, 6539158811108986, 47406388525312263, 51832461450964273,
    34899384416696791, 31274872882423837, 39018583255073131, 39873430349221998, 51832458512805894, 39018583255073131,
    33937680582472768, 33937768391741541, 34899384416696791, 34899294239773387, 39873430349221998, 34899294239773387,
    47406388233346408, 31274872882423837, 46670185173775187, 50941567015072889, 37661292141428126, 55136537924082815,
    32979468118427308, 33716433695698309, 38651893443419908, 33716433695698309, 32979468118427308, 42653660369595119,
    38689126349652458, 50941567693715774, 38651893443419908, 33716433695698309, 38689126349652458, 33716433695698309,
    38651893443419908, 33716433695698309, 46670185173775187, 10648357582030099, 12233320082730822, 13311322594732096,
    14678104925446590, 14420947085906609, 19227044757304335, 14192678098233476, 14420947085906609, 14272848446917460,
    13311322594732096, 13311322594732096, 14272848446917460, 19227044757304335, 14272848446917460, 10648357582030099,
    14678104925446590, 23417234838237829, 32302242698971809, 37548620482214717
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
noncomputable def negativeCeiling : ℝ := 54781218877 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 44101613899541672293281300480, coefficient := (-44101613899541672293281300480) }, { argument := 32611982909924236616873803776, coefficient := (-32611982909924236616873803776) }, { argument := 36383831467121879641957072896, coefficient := (-36383831467121879641957072896) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 36325803027780377441571176448, coefficient := (-36325803027780377441571176448) }, { argument := 36964115860536901645816037376, coefficient := (-36964115860536901645816037376) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 44101613899541672293281300480, coefficient := (-44101613899541672293281300480) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 105006146175336250217963978752, coefficient := (-105006146175336250217963978752) }, { argument := 2257331973009020418374993182720, coefficient := (-2257331973009020418374993182720) }, { argument := 73890954017223287938217934848, coefficient := (-73890954017223287938217934848) }, { argument := 95857161881299867821385187328, coefficient := (-95857161881299867821385187328) }, { argument := 1284084736222121465112569053184, coefficient := (-1284084736222121465112569053184) }, { argument := 2322353354038463547075651960832, coefficient := (-2322353354038463547075651960832) }, { argument := 2257327375785249344775377649664, coefficient := (-2257327375785249344775377649664) }, { argument := 1284084736222121465112569053184, coefficient := (-1284084736222121465112569053184) }, { argument := 75878645056026120356104241152, coefficient := (-75878645056026120356104241152) }, { argument := 75883263530446366869123235840, coefficient := (-75883263530446366869123235840) }, { argument := 73890954017223287938217934848, coefficient := (-73890954017223287938217934848) }, { argument := 73886335542803041425198940160, coefficient := (-73886335542803041425198940160) }, { argument := 2322353354038463547075651960832, coefficient := (-2322353354038463547075651960832) }, { argument := 73886335542803041425198940160, coefficient := (-73886335542803041425198940160) }, { argument := 105006124924687077304560517120, coefficient := (-105006124924687077304560517120) }, { argument := 95857161881299867821385187328, coefficient := (-95857161881299867821385187328) }, { argument := 63036984266073139911285800960, coefficient := (-63036984266073139911285800960) }, { argument := 4869332978323107755240380694528, coefficient := (-4869332978323107755240380694528) }, { argument := 1002393729357271016217608454144, coefficient := (-1002393729357271016217608454144) }, { argument := 44591445963484976923862116597760, coefficient := (-44591445963484976923862116597760) }, { argument := 624868818300636477642145529856, coefficient := (-624868818300636477642145529856) }, { argument := 32545250953158149877195079680, coefficient := (-32545250953158149877195079680) }, { argument := 995884679166639386242169438208, coefficient := (-995884679166639386242169438208) }, { argument := 1041448030501060796070242549760, coefficient := (-1041448030501060796070242549760) }, { argument := 624868818300636477642145529856, coefficient := (-624868818300636477642145529856) }, { argument := 15953682017238125069801028059136, coefficient := (-15953682017238125069801028059136) }, { argument := 1021920879929165906143925501952, coefficient := (-1021920879929165906143925501952) }, { argument := 4869335268854616826213535055872, coefficient := (-4869335268854616826213535055872) }, { argument := 995884679166639386242169438208, coefficient := (-995884679166639386242169438208) }, { argument := 32545250953158149877195079680, coefficient := (-32545250953158149877195079680) }, { argument := 1021920879929165906143925501952, coefficient := (-1021920879929165906143925501952) }, { argument := 32545250953158149877195079680, coefficient := (-32545250953158149877195079680) }, { argument := 995884679166639386242169438208, coefficient := (-995884679166639386242169438208) }, { argument := 1041448030501060796070242549760, coefficient := (-1041448030501060796070242549760) }, { argument := 63036984266073139911285800960, coefficient := (-63036984266073139911285800960) }, { argument := 242540742560184978175426560, coefficient := (-242540742560184978175426560) }, { argument := 181905556920138733631569920, coefficient := (-181905556920138733631569920) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 247593674696855498554081280, coefficient := (-247593674696855498554081280) }, { argument := 3314723481655861368397496320, coefficient := (-3314723481655861368397496320) }, { argument := 5795713160761086874316963840, coefficient := (-5795713160761086874316963840) }, { argument := 176852624783468213252915200, coefficient := (-176852624783468213252915200) }, { argument := 3314723481655861368397496320, coefficient := (-3314723481655861368397496320) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 5795713160761086874316963840, coefficient := (-5795713160761086874316963840) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 242540742560184978175426560, coefficient := (-242540742560184978175426560) }, { argument := 247593674696855498554081280, coefficient := (-247593674696855498554081280) }, { argument := 206637826122780004155654144, coefficient := (-206637826122780004155654144) }, { argument := 24423264384626594207124946944, coefficient := (-24423264384626594207124946944) }, { argument := 231771910558599867613455581184, coefficient := (-231771910558599867613455581184) }] }

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
def constantNumerator : ℤ := (-15326015389160500816372983398400000)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    21183819573, 11201859, 39161596399113, 523047525, 23602178059901117, 5902964925,
    523047525, 5900544835471811, 523047525, 523047525, 21684055965, 134497935,
    5902964925, 21684055965, 626589591166887, 523047525, 134497935, 523047525,
    290667, 137419893, 5216349567, 549679949, 290667, 4268506725,
    167047840155, 167047840155, 4268506725, 27915075966745, 5794065, 150345,
    102454147516869, 9332955, 13957214162833, 9332955, 9726165, 5794065,
    289125, 186528438472491, 4009829672620245, 32045100771, 2598214197, 556883116725,
    1007160460269, 4009821506310357, 556883116725, 16453562277, 16454563749, 32045100771,
    32043097827, 1007160460269, 32043097827, 186528400723755, 2598214197, 410986591894511,
    7813240446190607, 807436345485, 142569266876100685, 31458558915, 52430931525, 1604386504665,
    52430931525, 31458558915, 25701642633555, 1646331249885
  ]
def negativeCoefficients : Array ℕ := #[
    24423281135423134640004661248, 206637826122780004155654144, 176368150950279064750336770048, 9648523832062198541608550400, 6643422519731422921285280202752, 108890483247559097826725068800,
    9648523832062198541608550400, 6643422880578438161994365272064, 9648523832062198541608550400, 9648523832062198541608550400, 400000230866350002396400189440, 9924195941549689928511651840,
    108890483247559097826725068800, 400000230866350002396400189440, 176369290580838982820007247872, 9648523832062198541608550400, 9924195941549689928511651840, 9648523832062198541608550400,
    10723719519345868479135744, 1267474798403775348074348544, 12028083182681829456985718784, 1267475667706589821636968448, 10723719519345868479135744, 9842506391622889596203827200,
    385186094425653339530786242560, 385186094425653339530786242560, 9842506391622889596203827200, 62859162860925935194745077760, 213763268402875866367918080, 11093502951047450150830080,
    230706230289766528223136448512, 344325264672895856604610560, 62857704502864908081763975168, 344325264672895856604610560, 358832153147342522186465280, 213763268402875866367918080,
    10666829760622548221952000, 105006175749838869712645128192, 2257333427428961668629465661440, 73890971592358704164993236992, 95857184681475542926390984704, 1284085041649474779540042547200,
    2322353906467720008474021593088, 2257328830205190595029850128384, 1284085041649474779540042547200, 75878663106165196480900497408, 75883281580585442993919492096, 73890971592358704164993236992,
    73886353117938457651974242304, 2322353906467720008474021593088, 73886353117938457651974242304, 105006154499189696799241666560, 95857184681475542926390984704, 231364882763798731412243218432,
    17593853381010052794227712065536, 3723642905243280456040254013440, 160518724294422960820243073597440, 2321231940930876128440677826560, 120897496923483131689618636800, 3699463405858583829702330286080,
    3868719901551460214067796377600, 2321231940930876128440677826560, 59263952991891431154251055759360, 3796181403397370335054025195520
  ]
def negativeScales : Array ℕ := #[
    34, 23, 45, 28, 54, 32,
    28, 52, 28, 28, 34, 27,
    32, 34, 49, 28, 27, 28,
    18, 27, 32, 29, 18, 31,
    37, 37, 31, 44, 22, 17,
    46, 23, 43, 23, 23, 22,
    18, 47, 51, 34, 31, 39,
    39, 51, 39, 33, 33, 34,
    34, 39, 34, 47, 31, 48,
    52, 39, 56, 34, 35, 40,
    35, 34, 44, 40
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34302243688449809, 23417234838237829, 45154504810278656, 28962366810111394, 54389769518938547, 32458792623405399,
    28962366810111394, 52389769597300594, 28962366810111394, 28962366810111394, 34335915584407614, 27003008781783182,
    32458792623405399, 34335915584407614, 49154514132449561, 28962366810111394, 27003008781783182, 28962366810111394,
    18149007763183699, 27034015623917692, 32280393407159326, 29034016613395693, 18149007763183699, 31991084326739097,
    37281470373229352, 37281470373229352, 31991084326739097, 44666109715772095, 22466144438718846, 17197917363664646,
    46541971716686442, 23153902508801334, 43666076244273984, 23153902508801334, 23213439635778698, 22466144438718846,
    18141333835298278, 47406388931640691, 51832462380505801, 34899384759845151, 31274873225577085, 39018583598226868,
    39873430692402717, 51832459442349315, 39018583598226868, 33937680925663488, 33937768734911373, 34899384759845151,
    34899294582943196, 39873430692402717, 34899294582943196, 47406388639674918, 31274873225577085, 48546084656338922,
    52794842436544668, 39554557572704790, 56984440650439702, 34872733535386147, 35609699126903104, 40545158874702162,
    35609699126903104, 34872733535386147, 44546925800876414, 40582391780903437
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
noncomputable def negativeCeiling : ℝ := 89333477407 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 24423281135423134640004661248, coefficient := (-24423281135423134640004661248) }, { argument := 206637826122780004155654144, coefficient := (-206637826122780004155654144) }, { argument := 176368150950279064750336770048, coefficient := (-176368150950279064750336770048) }, { argument := 9648523832062198541608550400, coefficient := (-9648523832062198541608550400) }, { argument := 6643422519731422921285280202752, coefficient := (-6643422519731422921285280202752) }, { argument := 108890483247559097826725068800, coefficient := (-108890483247559097826725068800) }, { argument := 9648523832062198541608550400, coefficient := (-9648523832062198541608550400) }, { argument := 6643422880578438161994365272064, coefficient := (-6643422880578438161994365272064) }, { argument := 9648523832062198541608550400, coefficient := (-9648523832062198541608550400) }, { argument := 9648523832062198541608550400, coefficient := (-9648523832062198541608550400) }, { argument := 400000230866350002396400189440, coefficient := (-400000230866350002396400189440) }, { argument := 9924195941549689928511651840, coefficient := (-9924195941549689928511651840) }, { argument := 108890483247559097826725068800, coefficient := (-108890483247559097826725068800) }, { argument := 400000230866350002396400189440, coefficient := (-400000230866350002396400189440) }, { argument := 176369290580838982820007247872, coefficient := (-176369290580838982820007247872) }, { argument := 9648523832062198541608550400, coefficient := (-9648523832062198541608550400) }, { argument := 9924195941549689928511651840, coefficient := (-9924195941549689928511651840) }, { argument := 9648523832062198541608550400, coefficient := (-9648523832062198541608550400) }, { argument := 10723719519345868479135744, coefficient := (-10723719519345868479135744) }, { argument := 1267474798403775348074348544, coefficient := (-1267474798403775348074348544) }, { argument := 12028083182681829456985718784, coefficient := (-12028083182681829456985718784) }, { argument := 1267475667706589821636968448, coefficient := (-1267475667706589821636968448) }, { argument := 10723719519345868479135744, coefficient := (-10723719519345868479135744) }, { argument := 9842506391622889596203827200, coefficient := (-9842506391622889596203827200) }, { argument := 385186094425653339530786242560, coefficient := (-385186094425653339530786242560) }, { argument := 385186094425653339530786242560, coefficient := (-385186094425653339530786242560) }, { argument := 9842506391622889596203827200, coefficient := (-9842506391622889596203827200) }, { argument := 62859162860925935194745077760, coefficient := (-62859162860925935194745077760) }, { argument := 213763268402875866367918080, coefficient := (-213763268402875866367918080) }, { argument := 11093502951047450150830080, coefficient := (-11093502951047450150830080) }, { argument := 230706230289766528223136448512, coefficient := (-230706230289766528223136448512) }, { argument := 344325264672895856604610560, coefficient := (-344325264672895856604610560) }, { argument := 62857704502864908081763975168, coefficient := (-62857704502864908081763975168) }, { argument := 344325264672895856604610560, coefficient := (-344325264672895856604610560) }, { argument := 358832153147342522186465280, coefficient := (-358832153147342522186465280) }, { argument := 213763268402875866367918080, coefficient := (-213763268402875866367918080) }, { argument := 10666829760622548221952000, coefficient := (-10666829760622548221952000) }, { argument := 105006175749838869712645128192, coefficient := (-105006175749838869712645128192) }, { argument := 2257333427428961668629465661440, coefficient := (-2257333427428961668629465661440) }, { argument := 73890971592358704164993236992, coefficient := (-73890971592358704164993236992) }, { argument := 95857184681475542926390984704, coefficient := (-95857184681475542926390984704) }, { argument := 1284085041649474779540042547200, coefficient := (-1284085041649474779540042547200) }, { argument := 2322353906467720008474021593088, coefficient := (-2322353906467720008474021593088) }, { argument := 2257328830205190595029850128384, coefficient := (-2257328830205190595029850128384) }, { argument := 1284085041649474779540042547200, coefficient := (-1284085041649474779540042547200) }, { argument := 75878663106165196480900497408, coefficient := (-75878663106165196480900497408) }, { argument := 75883281580585442993919492096, coefficient := (-75883281580585442993919492096) }, { argument := 73890971592358704164993236992, coefficient := (-73890971592358704164993236992) }, { argument := 73886353117938457651974242304, coefficient := (-73886353117938457651974242304) }, { argument := 2322353906467720008474021593088, coefficient := (-2322353906467720008474021593088) }, { argument := 73886353117938457651974242304, coefficient := (-73886353117938457651974242304) }, { argument := 105006154499189696799241666560, coefficient := (-105006154499189696799241666560) }, { argument := 95857184681475542926390984704, coefficient := (-95857184681475542926390984704) }, { argument := 231364882763798731412243218432, coefficient := (-231364882763798731412243218432) }, { argument := 17593853381010052794227712065536, coefficient := (-17593853381010052794227712065536) }, { argument := 3723642905243280456040254013440, coefficient := (-3723642905243280456040254013440) }, { argument := 160518724294422960820243073597440, coefficient := (-160518724294422960820243073597440) }, { argument := 2321231940930876128440677826560, coefficient := (-2321231940930876128440677826560) }, { argument := 120897496923483131689618636800, coefficient := (-120897496923483131689618636800) }, { argument := 3699463405858583829702330286080, coefficient := (-3699463405858583829702330286080) }, { argument := 3868719901551460214067796377600, coefficient := (-3868719901551460214067796377600) }, { argument := 2321231940930876128440677826560, coefficient := (-2321231940930876128440677826560) }, { argument := 59263952991891431154251055759360, coefficient := (-59263952991891431154251055759360) }, { argument := 3796181403397370335054025195520, coefficient := (-3796181403397370335054025195520) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7
