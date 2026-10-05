import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 21, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21

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
def constantNumerator : ℤ := (-3806123484295189161477775986524160)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    881609, 9492213, 4345, 543514963, 1375, 165,
    4345, 8635, 1375, 133265, 8525, 75937761,
    4345, 165, 8525, 165, 4345, 4345,
    881609, 1388433979809513, 40240157373, 21574604266942347, 421049451537, 18647877807,
    43149195803714841, 18647877807, 36314288361, 686045609847, 36314288361, 421049451537,
    686045609847, 173554807882653, 36314288361, 36314288361, 40240157373, 235831455323085,
    1078936635, 893976069, 13784715313620725, 6011218395, 3773301744647227, 24075700341,
    24075700341, 17232159399, 893976069, 52512255, 8220499005, 2055125505,
    210052035, 2209251205, 8206817675, 138049135, 2680541507369, 24505719,
    2680541796567, 24505719, 1830522427, 6799934645, 114383569, 38864425497,
    38864416231, 852925, 1388434125938967, 40240147779
  ]
def negativeCoefficients : Array ℕ := #[
    8326561585192450094402633728, 358605668155676188822663593984, 168089045959218040451146711040, 2566676844209335352145108533248, 106385472126087367374143488000, 6383128327565242042448609280,
    168089045959218040451146711040, 167025191237957166777405276160, 106385472126087367374143488000, 2577719989615096911475496714240, 164897481795435419429922406400, 358605937330565712392440774656,
    168089045959218040451146711040, 6383128327565242042448609280, 164897481795435419429922406400, 6383128327565242042448609280, 168089045959218040451146711040, 168089045959218040451146711040,
    8326561585192450094402633728, 390809422131166094602197270528, 92787485568190933615138308096, 12145422467158433370273705099264, 970873934359851476119374004224, 85998157355884279935981846528,
    12145418883934170474403590045696, 85998157355884279935981846528, 83735047951782062042929692672, 3163826946934900614486911090688, 83735047951782062042929692672, 970873934359851476119374004224,
    3163826946934900614486911090688, 390810684054337036335861202944, 83735047951782062042929692672, 83735047951782062042929692672, 92787485568190933615138308096, 4248361817261149525442706800640,
    159222943820755004703406817280, 8245473876431955600712138752, 15520209687457666753576199782400, 221774814607480185122602352640, 4248360082787423491742287003648, 222059141292874390488144150528,
    222059141292874390488144150528, 158938617135360799337865019392, 8245473876431955600712138752, 3874720514873499081580216320, 151641441303419015718324142080, 151641496920352397952622264320,
    3874776131806881315878338560, 163013966292677742910630789120, 605556261241284204074054451200, 162979652028286709876905738240, 386306743479621633845669920768, 3616405813881932476141535232,
    386306785157445795007036391424, 3616405813881932476141535232, 8441794683013668829300523008, 31359163528566503425263534080, 8440017694321990332911190016, 89615263839363893149663494144,
    89615242473422569775575334912, 8055648864803184287783321600, 390809463262950755993074532352, 92787463445933103218958532608
  ]
def negativeScales : Array ℕ := #[
    19, 23, 12, 29, 10, 7,
    12, 13, 10, 17, 13, 26,
    12, 7, 13, 7, 12, 12,
    19, 50, 35, 54, 38, 34,
    55, 34, 35, 39, 35, 38,
    39, 47, 35, 35, 35, 47,
    30, 29, 53, 32, 51, 34,
    34, 34, 29, 25, 32, 30,
    27, 31, 32, 27, 41, 24,
    41, 24, 30, 32, 26, 35,
    35, 19, 50, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19749779426551864, 23178313043496568, 12085140461701763, 29017744512380458, 10425215903299403, 7366322214245818,
    12085140461701763, 13075980462416287, 10425215903299403, 17023938402976007, 13057484118798898, 26178314126405085,
    12085140461701763, 7366322214245818, 13057484118798898, 7366322214245818, 12085140461701763, 12085140461701763,
    19749779426551864, 50302380001788130, 35227916896184129, 54260183615152163, 38615198729074156, 34118292405009631,
    55260183189518502, 34118292405009631, 35079818257194995, 39319513536941482, 35079818257194995, 38615198729074156,
    39319513536941482, 47302384660241224, 35079818257194995, 35079818257194995, 35227916896184129, 47744749487195856,
    30006962993088730, 29735660971435185, 53613918990859313, 32485010289893537, 51744748898188311, 34486858714285916,
    34486858714285916, 34004384448986954, 29735660971435185, 25646150813952695, 32936578834070289, 30936579363201838,
    27646171521949016, 31040910325012068, 32934175764275334, 27040606607292031, 41285661613615271, 24546615140383668,
    41285661769264604, 24546615140383668, 30769608303537831, 32662873734527600, 26769304585815586, 35177731139015913,
    35177730795050611, 19702059361560245, 50302380153628427, 35227916552218828
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
noncomputable def negativeCeiling : ℝ := 39263557 / 1000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 8326561585192450094402633728, coefficient := (-8326561585192450094402633728) }, { argument := 358605668155676188822663593984, coefficient := (-358605668155676188822663593984) }, { argument := 168089045959218040451146711040, coefficient := (-168089045959218040451146711040) }, { argument := 2566676844209335352145108533248, coefficient := (-2566676844209335352145108533248) }, { argument := 106385472126087367374143488000, coefficient := (-106385472126087367374143488000) }, { argument := 6383128327565242042448609280, coefficient := (-6383128327565242042448609280) }, { argument := 168089045959218040451146711040, coefficient := (-168089045959218040451146711040) }, { argument := 167025191237957166777405276160, coefficient := (-167025191237957166777405276160) }, { argument := 106385472126087367374143488000, coefficient := (-106385472126087367374143488000) }, { argument := 2577719989615096911475496714240, coefficient := (-2577719989615096911475496714240) }, { argument := 164897481795435419429922406400, coefficient := (-164897481795435419429922406400) }, { argument := 358605937330565712392440774656, coefficient := (-358605937330565712392440774656) }, { argument := 168089045959218040451146711040, coefficient := (-168089045959218040451146711040) }, { argument := 6383128327565242042448609280, coefficient := (-6383128327565242042448609280) }, { argument := 164897481795435419429922406400, coefficient := (-164897481795435419429922406400) }, { argument := 6383128327565242042448609280, coefficient := (-6383128327565242042448609280) }, { argument := 168089045959218040451146711040, coefficient := (-168089045959218040451146711040) }, { argument := 168089045959218040451146711040, coefficient := (-168089045959218040451146711040) }, { argument := 8326561585192450094402633728, coefficient := (-8326561585192450094402633728) }, { argument := 390809422131166094602197270528, coefficient := (-390809422131166094602197270528) }, { argument := 92787485568190933615138308096, coefficient := (-92787485568190933615138308096) }, { argument := 12145422467158433370273705099264, coefficient := (-12145422467158433370273705099264) }, { argument := 970873934359851476119374004224, coefficient := (-970873934359851476119374004224) }, { argument := 85998157355884279935981846528, coefficient := (-85998157355884279935981846528) }, { argument := 12145418883934170474403590045696, coefficient := (-12145418883934170474403590045696) }, { argument := 85998157355884279935981846528, coefficient := (-85998157355884279935981846528) }, { argument := 83735047951782062042929692672, coefficient := (-83735047951782062042929692672) }, { argument := 3163826946934900614486911090688, coefficient := (-3163826946934900614486911090688) }, { argument := 83735047951782062042929692672, coefficient := (-83735047951782062042929692672) }, { argument := 970873934359851476119374004224, coefficient := (-970873934359851476119374004224) }, { argument := 3163826946934900614486911090688, coefficient := (-3163826946934900614486911090688) }, { argument := 390810684054337036335861202944, coefficient := (-390810684054337036335861202944) }, { argument := 83735047951782062042929692672, coefficient := (-83735047951782062042929692672) }, { argument := 83735047951782062042929692672, coefficient := (-83735047951782062042929692672) }, { argument := 92787485568190933615138308096, coefficient := (-92787485568190933615138308096) }, { argument := 4248361817261149525442706800640, coefficient := (-4248361817261149525442706800640) }, { argument := 159222943820755004703406817280, coefficient := (-159222943820755004703406817280) }, { argument := 8245473876431955600712138752, coefficient := (-8245473876431955600712138752) }, { argument := 15520209687457666753576199782400, coefficient := (-15520209687457666753576199782400) }, { argument := 221774814607480185122602352640, coefficient := (-221774814607480185122602352640) }, { argument := 4248360082787423491742287003648, coefficient := (-4248360082787423491742287003648) }, { argument := 222059141292874390488144150528, coefficient := (-222059141292874390488144150528) }, { argument := 222059141292874390488144150528, coefficient := (-222059141292874390488144150528) }, { argument := 158938617135360799337865019392, coefficient := (-158938617135360799337865019392) }, { argument := 8245473876431955600712138752, coefficient := (-8245473876431955600712138752) }, { argument := 3874720514873499081580216320, coefficient := (-3874720514873499081580216320) }, { argument := 151641441303419015718324142080, coefficient := (-151641441303419015718324142080) }, { argument := 151641496920352397952622264320, coefficient := (-151641496920352397952622264320) }, { argument := 3874776131806881315878338560, coefficient := (-3874776131806881315878338560) }, { argument := 163013966292677742910630789120, coefficient := (-163013966292677742910630789120) }, { argument := 605556261241284204074054451200, coefficient := (-605556261241284204074054451200) }, { argument := 162979652028286709876905738240, coefficient := (-162979652028286709876905738240) }, { argument := 386306743479621633845669920768, coefficient := (-386306743479621633845669920768) }, { argument := 3616405813881932476141535232, coefficient := (-3616405813881932476141535232) }, { argument := 386306785157445795007036391424, coefficient := (-386306785157445795007036391424) }, { argument := 3616405813881932476141535232, coefficient := (-3616405813881932476141535232) }, { argument := 8441794683013668829300523008, coefficient := (-8441794683013668829300523008) }, { argument := 31359163528566503425263534080, coefficient := (-31359163528566503425263534080) }, { argument := 8440017694321990332911190016, coefficient := (-8440017694321990332911190016) }, { argument := 89615263839363893149663494144, coefficient := (-89615263839363893149663494144) }, { argument := 89615242473422569775575334912, coefficient := (-89615242473422569775575334912) }, { argument := 8055648864803184287783321600, coefficient := (-8055648864803184287783321600) }, { argument := 390809463262950755993074532352, coefficient := (-390809463262950755993074532352) }, { argument := 92787463445933103218958532608, coefficient := (-92787463445933103218958532608) }] }

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
def constantNumerator : ℤ := (-10951906240931478135829307429224448)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    21574608432058485, 421049351151, 18647873361, 43149204133944039, 18647873361, 36314279703,
    686045446281, 36314279703, 421049351151, 686045446281, 173554826148963, 36314279703,
    36314279703, 40240147779, 27570985564125875, 4007980725, 3320898315, 100749567541912825,
    22330178325, 6892732200998933, 89435227035, 89435227035, 64013177865, 3320898315,
    41896359606283, 3836232869, 41896367727349, 3836232869, 12308685285, 45723698475,
    769130895, 406654598493, 406654501539, 9383691, 18010343523, 18010339229,
    4187, 7546603601931181, 67419345, 55861743, 27569375337295133, 375622065,
    3773300260443035, 1504414527, 1504414527, 1076783253, 55861743, 83792694374681,
    959058569, 83792710616807, 959058569, 16992001, 18010343523, 18010339229,
    1325, 159, 52512255, 8220499005, 2055125505, 210052035,
    49297862603, 183129274405, 3080467841, 35072774229
  ]
def negativeCoefficients : Array ℕ := #[
    12145424811910369251728629432320, 970873702885495153193492938752, 85998136852328242007815225344, 12145421228685239975880198979584, 85998136852328242007815225344, 83735027987793288270767456256,
    3163826192619865324392781185024, 83735027987793288270767456256, 970873702885495153193492938752, 3163826192619865324392781185024, 390810725186410491052843597824, 83735027987793288270767456256,
    83735027987793288270767456256, 92787463445933103218958532608, 15521085039104326887326875648000, 591473557491486897002564812800, 30629880655809142880489963520, 56716964354937152164065601126400,
    823838169363142463682143846400, 15521053085991706697869645840384, 824894372144377261712505569280, 824894372144377261712505569280, 590417354710252098972203089920, 30629880655809142880489963520,
    12075803488706330835528347287552, 141532011883191081337102532608, 12075805829444238768405433286656, 141532011883191081337102532608, 227055167336229713339807170560, 843453363871788712817432985600,
    227007372467970774471404421120, 937681663099685613687942414336, 937681439538982498383458992128, 354505822912044351719617855488, 83058049412093364382614945792, 83058029609513601255411286016,
    161976717015246475343832285184, 4248360146196263709921322729472, 159189427562512600344884674560, 8243738213058688232145813504, 15520178561984962931585236074496, 221728131247785407623232225280,
    4248358411722061983510261923840, 222012398082718465838133805056, 222012398082718465838133805056, 158905160727579542129983094784, 8243738213058688232145813504, 12075799909189862654048921976832,
    141532063792328904755780780032, 12075802249926905895797552840704, 141532063792328904755780780032, 2567758591977199818904564662272, 83058049412093364382614945792, 83058029609513601255411286016,
    102516909503320554015083724800, 6151014570199233240905023488, 3874720514873499081580216320, 151641441303419015718324142080, 151641496920352397952622264320, 3874776131806881315878338560,
    227346263704609495023576154112, 844534714338291006038993797120, 227298407560878429310470324224, 80872311269669854793598763008
  ]
def negativeScales : Array ℕ := #[
    54, 38, 34, 55, 34, 35,
    39, 35, 38, 39, 47, 35,
    35, 35, 54, 31, 31, 56,
    34, 52, 36, 36, 35, 31,
    45, 31, 45, 31, 33, 35,
    29, 38, 38, 23, 34, 34,
    12, 52, 26, 25, 54, 28,
    51, 30, 30, 30, 25, 46,
    29, 46, 29, 24, 34, 34,
    10, 7, 25, 32, 30, 27,
    35, 37, 31, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    54260183893673695, 38615198385108854, 34118292061044329, 55260183468040012, 34118292061044329, 35079817913229694,
    39319513192976181, 35079817913229694, 38615198385108854, 39319513192976181, 47302384812082096, 35079817913229694,
    35079817913229694, 35227916552218828, 54614000357663850, 31900228428777727, 31628926402587145, 56483551259218441,
    34378275721196839, 52613997387598003, 36380124145589208, 36380124145589208, 35897649884477577, 31628926402587145,
    45251890126478735, 31837043153573873, 45251890406126433, 31837043153573873, 33518957621817216, 35412223053120185,
    29518653904097175, 38565012971899457, 38565012627934155, 23161724076285288, 34068106647841414, 34068106303876113,
    12031701202740303, 52744748919721236, 26006659275368693, 25735357253714041, 54613916097560121, 28484706572173498,
    51744748330713297, 30486554996565878, 30486554996565878, 30004080731266917, 25735357253714041, 46251889698834195,
    29837043682705360, 46251889978481873, 29837043682705360, 24018352420370608, 34068106647841414, 34068106303876113,
    10371776644337926, 7312882955284356, 25646150813952695, 32936578834070289, 30936579363201838, 27646171521949016,
    35520806046209616, 37414071477512555, 31520502328489574, 35029632500026779
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
noncomputable def negativeCeiling : ℝ := 126389087361 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 12145424811910369251728629432320, coefficient := (-12145424811910369251728629432320) }, { argument := 970873702885495153193492938752, coefficient := (-970873702885495153193492938752) }, { argument := 85998136852328242007815225344, coefficient := (-85998136852328242007815225344) }, { argument := 12145421228685239975880198979584, coefficient := (-12145421228685239975880198979584) }, { argument := 85998136852328242007815225344, coefficient := (-85998136852328242007815225344) }, { argument := 83735027987793288270767456256, coefficient := (-83735027987793288270767456256) }, { argument := 3163826192619865324392781185024, coefficient := (-3163826192619865324392781185024) }, { argument := 83735027987793288270767456256, coefficient := (-83735027987793288270767456256) }, { argument := 970873702885495153193492938752, coefficient := (-970873702885495153193492938752) }, { argument := 3163826192619865324392781185024, coefficient := (-3163826192619865324392781185024) }, { argument := 390810725186410491052843597824, coefficient := (-390810725186410491052843597824) }, { argument := 83735027987793288270767456256, coefficient := (-83735027987793288270767456256) }, { argument := 83735027987793288270767456256, coefficient := (-83735027987793288270767456256) }, { argument := 92787463445933103218958532608, coefficient := (-92787463445933103218958532608) }, { argument := 15521085039104326887326875648000, coefficient := (-15521085039104326887326875648000) }, { argument := 591473557491486897002564812800, coefficient := (-591473557491486897002564812800) }, { argument := 30629880655809142880489963520, coefficient := (-30629880655809142880489963520) }, { argument := 56716964354937152164065601126400, coefficient := (-56716964354937152164065601126400) }, { argument := 823838169363142463682143846400, coefficient := (-823838169363142463682143846400) }, { argument := 15521053085991706697869645840384, coefficient := (-15521053085991706697869645840384) }, { argument := 824894372144377261712505569280, coefficient := (-824894372144377261712505569280) }, { argument := 824894372144377261712505569280, coefficient := (-824894372144377261712505569280) }, { argument := 590417354710252098972203089920, coefficient := (-590417354710252098972203089920) }, { argument := 30629880655809142880489963520, coefficient := (-30629880655809142880489963520) }, { argument := 12075803488706330835528347287552, coefficient := (-12075803488706330835528347287552) }, { argument := 141532011883191081337102532608, coefficient := (-141532011883191081337102532608) }, { argument := 12075805829444238768405433286656, coefficient := (-12075805829444238768405433286656) }, { argument := 141532011883191081337102532608, coefficient := (-141532011883191081337102532608) }, { argument := 227055167336229713339807170560, coefficient := (-227055167336229713339807170560) }, { argument := 843453363871788712817432985600, coefficient := (-843453363871788712817432985600) }, { argument := 227007372467970774471404421120, coefficient := (-227007372467970774471404421120) }, { argument := 937681663099685613687942414336, coefficient := (-937681663099685613687942414336) }, { argument := 937681439538982498383458992128, coefficient := (-937681439538982498383458992128) }, { argument := 354505822912044351719617855488, coefficient := (-354505822912044351719617855488) }, { argument := 83058049412093364382614945792, coefficient := (-83058049412093364382614945792) }, { argument := 83058029609513601255411286016, coefficient := (-83058029609513601255411286016) }, { argument := 161976717015246475343832285184, coefficient := (-161976717015246475343832285184) }, { argument := 4248360146196263709921322729472, coefficient := (-4248360146196263709921322729472) }, { argument := 159189427562512600344884674560, coefficient := (-159189427562512600344884674560) }, { argument := 8243738213058688232145813504, coefficient := (-8243738213058688232145813504) }, { argument := 15520178561984962931585236074496, coefficient := (-15520178561984962931585236074496) }, { argument := 221728131247785407623232225280, coefficient := (-221728131247785407623232225280) }, { argument := 4248358411722061983510261923840, coefficient := (-4248358411722061983510261923840) }, { argument := 222012398082718465838133805056, coefficient := (-222012398082718465838133805056) }, { argument := 222012398082718465838133805056, coefficient := (-222012398082718465838133805056) }, { argument := 158905160727579542129983094784, coefficient := (-158905160727579542129983094784) }, { argument := 8243738213058688232145813504, coefficient := (-8243738213058688232145813504) }, { argument := 12075799909189862654048921976832, coefficient := (-12075799909189862654048921976832) }, { argument := 141532063792328904755780780032, coefficient := (-141532063792328904755780780032) }, { argument := 12075802249926905895797552840704, coefficient := (-12075802249926905895797552840704) }, { argument := 141532063792328904755780780032, coefficient := (-141532063792328904755780780032) }, { argument := 2567758591977199818904564662272, coefficient := (-2567758591977199818904564662272) }, { argument := 83058049412093364382614945792, coefficient := (-83058049412093364382614945792) }, { argument := 83058029609513601255411286016, coefficient := (-83058029609513601255411286016) }, { argument := 102516909503320554015083724800, coefficient := (-102516909503320554015083724800) }, { argument := 6151014570199233240905023488, coefficient := (-6151014570199233240905023488) }, { argument := 3874720514873499081580216320, coefficient := (-3874720514873499081580216320) }, { argument := 151641441303419015718324142080, coefficient := (-151641441303419015718324142080) }, { argument := 151641496920352397952622264320, coefficient := (-151641496920352397952622264320) }, { argument := 3874776131806881315878338560, coefficient := (-3874776131806881315878338560) }, { argument := 227346263704609495023576154112, coefficient := (-227346263704609495023576154112) }, { argument := 844534714338291006038993797120, coefficient := (-844534714338291006038993797120) }, { argument := 227298407560878429310470324224, coefficient := (-227298407560878429310470324224) }, { argument := 80872311269669854793598763008, coefficient := (-80872311269669854793598763008) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21
