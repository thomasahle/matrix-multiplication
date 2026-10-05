import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 4, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4

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
def constantNumerator : ℤ := (-1522079654025956223539762398494720)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    20054955933, 159293471053, 15208540865, 1233124935, 264299777735, 478041433135,
    159293472031, 264299777735, 7809791255, 7809791255, 15208540865, 15208540865,
    478041433135, 15208540865, 20054954955, 1233124935, 2452652827767, 23133973288179,
    103862374231, 322593932734013, 4046586009, 6744310015, 206375886459, 6744310015,
    4046586009, 3306060769353, 211771334471, 23133973423347, 206375886459, 6744310015,
    211771334471, 6744310015, 206375886459, 6744310015, 2452652827767, 25442995,
    4462462285, 1115615705, 6360615, 2838165, 1828467135, 19446516903,
    914236323, 2838165, 74779392319451, 722370075, 642956249128959, 8152462275,
    722370075, 1285912311240743, 722370075, 722370075, 29947399395, 185752305,
    8152462275, 29947399395, 74779543547867, 722370075, 185752305, 722370075,
    73645, 47445255, 504600239, 23722699
  ]
def negativeCoefficients : Array ℕ := #[
    23121789969098372593754308608, 183652868320471984917056585728, 17534253816950517993297674240, 22747140086854726045359144960, 304716897413491434315956879360, 551144248354417633140680949760,
    183652869448029216422552928256, 304716897413491434315956879360, 18008152568759991452575989760, 18008152568759991452575989760, 17534253816950517993297674240, 17534253816950517993297674240,
    551144248354417633140680949760, 17534253816950517993297674240, 23121788841541141088257966080, 22747140086854726045359144960, 22091532722401309009970724864, 833489227841935619812881334272,
    478980659081775724585050701824, 5811335661011535194861487521792, 298585345921106945195875762176, 15551320100057653395618529280, 475870395061764193905926995968, 497642243201844908659792936960,
    298585345921106945195875762176, 7623257113048261694532203053056, 488311451141810316622421819392, 833489232711876055272202960896, 475870395061764193905926995968, 15551320100057653395618529280,
    488311451141810316622421819392, 15551320100057653395618529280, 475870395061764193905926995968, 497642243201844908659792936960, 22091532722401309009970724864, 58667552154208969152266240,
    10289737463747016766332600320, 10289738697373026695658864640, 58666318528199039826001920, 104709806787919739124449280, 33729265286533932665442140160, 358724920434707873413094965248,
    33729366946540522878781095936, 104709806787919739124449280, 42097055423108956772695539712, 6662687950015687164533145600, 1447808761996355772887787896832, 75193192578748469428302643200,
    6662687950015687164533145600, 1447808551433735862417077829632, 6662687950015687164533145600, 6662687950015687164533145600, 276216006156364630735359836160, 6853050462873278226376949760,
    75193192578748469428302643200, 276216006156364630735359836160, 42097140557138699951489941504, 6662687950015687164533145600, 6853050462873278226376949760, 6662687950015687164533145600,
    5434041869233359715041280, 1750420952993776944713564160, 18616462936731346724032872448, 1750426228762582025645326336
  ]
def negativeScales : Array ℕ := #[
    34, 37, 33, 30, 37, 38,
    37, 37, 32, 32, 33, 33,
    38, 33, 34, 30, 41, 44,
    36, 48, 31, 32, 37, 32,
    31, 41, 37, 44, 37, 32,
    37, 32, 37, 32, 41, 24,
    32, 30, 22, 21, 30, 34,
    29, 21, 46, 29, 49, 32,
    29, 50, 29, 29, 34, 27,
    32, 34, 46, 29, 27, 29,
    16, 25, 28, 24
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34223239744978067, 37212896180225653, 33824162694845096, 30199671828888320, 37943384264813295, 38798344710264954,
    37212896189083239, 37943384264813295, 32862636843811109, 32862636843811109, 33824162694845096, 33824162694845096,
    38798344710264954, 33824162694845096, 34223239674623598, 30199671828888320, 41157480173968341, 44395078305426975,
    36595882153816596, 48196712633324364, 31914058119445301, 32651023708025882, 37586483455813176, 32651023708025882,
    31914058119445301, 41588250381987562, 37623716362019036, 44395078313856405, 37586483455813176, 32651023708025882,
    37623716362019036, 32651023708025882, 37586483455813176, 32651023708025882, 41157480173968341, 24600765170426203,
    32055192830080739, 30055193003043949, 22600734833983421, 21436527033903115, 30767987550125517, 34178792723788737,
    29767991898401891, 21436527033903115, 46087705980991800, 29428162887876544, 49191713899083367, 32924588720739138,
    29428162887876544, 50191713689264448, 29428162887876544, 29428162887876544, 34801711675667251, 27468804872373962,
    32924588720739138, 34801711675667251, 46087708898590599, 29428162887876544, 27468804872373962, 29428162887876544,
    16168299958848971, 25499760474740145, 28910565654006687, 24499764823016489
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
noncomputable def negativeCeiling : ℝ := 6675181043 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 23121789969098372593754308608, coefficient := (-23121789969098372593754308608) }, { argument := 183652868320471984917056585728, coefficient := (-183652868320471984917056585728) }, { argument := 17534253816950517993297674240, coefficient := (-17534253816950517993297674240) }, { argument := 22747140086854726045359144960, coefficient := (-22747140086854726045359144960) }, { argument := 304716897413491434315956879360, coefficient := (-304716897413491434315956879360) }, { argument := 551144248354417633140680949760, coefficient := (-551144248354417633140680949760) }, { argument := 183652869448029216422552928256, coefficient := (-183652869448029216422552928256) }, { argument := 304716897413491434315956879360, coefficient := (-304716897413491434315956879360) }, { argument := 18008152568759991452575989760, coefficient := (-18008152568759991452575989760) }, { argument := 18008152568759991452575989760, coefficient := (-18008152568759991452575989760) }, { argument := 17534253816950517993297674240, coefficient := (-17534253816950517993297674240) }, { argument := 17534253816950517993297674240, coefficient := (-17534253816950517993297674240) }, { argument := 551144248354417633140680949760, coefficient := (-551144248354417633140680949760) }, { argument := 17534253816950517993297674240, coefficient := (-17534253816950517993297674240) }, { argument := 23121788841541141088257966080, coefficient := (-23121788841541141088257966080) }, { argument := 22747140086854726045359144960, coefficient := (-22747140086854726045359144960) }, { argument := 22091532722401309009970724864, coefficient := (-22091532722401309009970724864) }, { argument := 833489227841935619812881334272, coefficient := (-833489227841935619812881334272) }, { argument := 478980659081775724585050701824, coefficient := (-478980659081775724585050701824) }, { argument := 5811335661011535194861487521792, coefficient := (-5811335661011535194861487521792) }, { argument := 298585345921106945195875762176, coefficient := (-298585345921106945195875762176) }, { argument := 15551320100057653395618529280, coefficient := (-15551320100057653395618529280) }, { argument := 475870395061764193905926995968, coefficient := (-475870395061764193905926995968) }, { argument := 497642243201844908659792936960, coefficient := (-497642243201844908659792936960) }, { argument := 298585345921106945195875762176, coefficient := (-298585345921106945195875762176) }, { argument := 7623257113048261694532203053056, coefficient := (-7623257113048261694532203053056) }, { argument := 488311451141810316622421819392, coefficient := (-488311451141810316622421819392) }, { argument := 833489232711876055272202960896, coefficient := (-833489232711876055272202960896) }, { argument := 475870395061764193905926995968, coefficient := (-475870395061764193905926995968) }, { argument := 15551320100057653395618529280, coefficient := (-15551320100057653395618529280) }, { argument := 488311451141810316622421819392, coefficient := (-488311451141810316622421819392) }, { argument := 15551320100057653395618529280, coefficient := (-15551320100057653395618529280) }, { argument := 475870395061764193905926995968, coefficient := (-475870395061764193905926995968) }, { argument := 497642243201844908659792936960, coefficient := (-497642243201844908659792936960) }, { argument := 22091532722401309009970724864, coefficient := (-22091532722401309009970724864) }, { argument := 58667552154208969152266240, coefficient := (-58667552154208969152266240) }, { argument := 10289737463747016766332600320, coefficient := (-10289737463747016766332600320) }, { argument := 10289738697373026695658864640, coefficient := (-10289738697373026695658864640) }, { argument := 58666318528199039826001920, coefficient := (-58666318528199039826001920) }, { argument := 104709806787919739124449280, coefficient := (-104709806787919739124449280) }, { argument := 33729265286533932665442140160, coefficient := (-33729265286533932665442140160) }, { argument := 358724920434707873413094965248, coefficient := (-358724920434707873413094965248) }, { argument := 33729366946540522878781095936, coefficient := (-33729366946540522878781095936) }, { argument := 104709806787919739124449280, coefficient := (-104709806787919739124449280) }, { argument := 42097055423108956772695539712, coefficient := (-42097055423108956772695539712) }, { argument := 6662687950015687164533145600, coefficient := (-6662687950015687164533145600) }, { argument := 1447808761996355772887787896832, coefficient := (-1447808761996355772887787896832) }, { argument := 75193192578748469428302643200, coefficient := (-75193192578748469428302643200) }, { argument := 6662687950015687164533145600, coefficient := (-6662687950015687164533145600) }, { argument := 1447808551433735862417077829632, coefficient := (-1447808551433735862417077829632) }, { argument := 6662687950015687164533145600, coefficient := (-6662687950015687164533145600) }, { argument := 6662687950015687164533145600, coefficient := (-6662687950015687164533145600) }, { argument := 276216006156364630735359836160, coefficient := (-276216006156364630735359836160) }, { argument := 6853050462873278226376949760, coefficient := (-6853050462873278226376949760) }, { argument := 75193192578748469428302643200, coefficient := (-75193192578748469428302643200) }, { argument := 276216006156364630735359836160, coefficient := (-276216006156364630735359836160) }, { argument := 42097140557138699951489941504, coefficient := (-42097140557138699951489941504) }, { argument := 6662687950015687164533145600, coefficient := (-6662687950015687164533145600) }, { argument := 6853050462873278226376949760, coefficient := (-6853050462873278226376949760) }, { argument := 6662687950015687164533145600, coefficient := (-6662687950015687164533145600) }, { argument := 5434041869233359715041280, coefficient := (-5434041869233359715041280) }, { argument := 1750420952993776944713564160, coefficient := (-1750420952993776944713564160) }, { argument := 18616462936731346724032872448, coefficient := (-18616462936731346724032872448) }, { argument := 1750426228762582025645326336, coefficient := (-1750426228762582025645326336) }] }

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
def constantNumerator : ℤ := (-11387326226683935045965128073740288)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    73645, 726027645, 113655555895, 28413899395, 2904152265, 9832160204049,
    2838165, 73645, 70746681410153, 4571655, 19669335430005, 4571655,
    4764265, 2838165, 141625, 20054969751, 159293481343, 15208551743,
    1233125817, 264299966777, 478041775057, 159293482321, 264299966777, 7809796841,
    7809796841, 15208551743, 15208551743, 478041775057, 15208551743, 20054968773,
    1233125817, 17647960265695, 169353980177211, 372283758077, 2386061583861301, 14504562003,
    24174270005, 739732662153, 24174270005, 14504562003, 11850227156451, 759072078157,
    169353986248507, 739732662153, 24174270005, 759072078157, 24174270005, 739732662153,
    24174270005, 17647960265695, 642449783826431, 113082983825, 5420418991709267, 1276222246025,
    113082983825, 10840835376723803, 113082983825, 113082983825, 4688097415145, 29078481555,
    1276222246025, 4688097415145, 642449820413951, 113082983825
  ]
def negativeCoefficients : Array ℕ := #[
    5434041869233359715041280, 6696423078876526086885212160, 262071869018781992960959447040, 262071965137847832033791836160, 6696519197942365159717601280, 22140056515601048158341169152,
    104709806787919739124449280, 5434041869233359715041280, 79653682009116061822166761472, 168664299556589280386088960, 22145702928298953176902533120, 168664299556589280386088960,
    175770354308663673859604480, 104709806787919739124449280, 5225040258878230495232000, 23121805900167723251165822976, 183652880184034267321511968768, 17534266358430645106579079168,
    22747156356882999057183670272, 304717115364078508203522916352, 551144642563644331323012677632, 183652881311591498827008311296, 304717115364078508203522916352, 18008165449199040920270405632,
    18008165449199040920270405632, 17534266358430645106579079168, 17534266358430645106579079168, 551144642563644331323012677632, 17534266358430645106579079168, 23121804772610491745669480448,
    22747156356882999057183670272, 79479347276433321582363934720, 3050810088079191302960131866624, 1716855802011305042443772100608, 21491732119921621351818007150592, 1070247772682371974510403387392,
    55742071493873540339083509760, 1705707387712530334375955398656, 1783746287803953290850672312320, 1070247772682371974510403387392, 27324763446296809474218736484352, 1750301044907629166647222206464,
    3050810197449936915984063397888, 1705707387712530334375955398656, 55742071493873540339083509760, 1750301044907629166647222206464, 55742071493873540339083509760, 1705707387712530334375955398656,
    1783746287803953290850672312320, 79479347276433321582363934720, 1446668303522485179724897189888, 260751607713901479142516326400, 48822793902507629016791451172864, 2942768144199745264608398540800,
    260751607713901479142516326400, 48822782162998209816556143116288, 260751607713901479142516326400, 260751607713901479142516326400, 10810016651224887035308319703040, 268201653648584378546588221440,
    2942768144199745264608398540800, 10810016651224887035308319703040, 1446668385910255898930182094848, 260751607713901479142516326400
  ]
def negativeScales : Array ℕ := #[
    16, 29, 36, 34, 31, 43,
    21, 16, 46, 22, 44, 22,
    22, 21, 17, 34, 37, 33,
    30, 37, 38, 37, 37, 32,
    32, 33, 33, 38, 33, 34,
    30, 44, 47, 38, 51, 33,
    34, 39, 34, 33, 43, 39,
    47, 39, 34, 39, 34, 39,
    34, 44, 49, 36, 52, 40,
    36, 53, 36, 36, 42, 34,
    40, 42, 49, 36
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16168299958848971, 29435449241955043, 36725877253928141, 34725877783059616, 31435469949951353, 43160645561651849,
    21436527033903115, 16168299958848971, 46007727709036352, 22124285103985659, 44161013447479913, 22124285103985659,
    22183822230963023, 21436527033903115, 17111716430482603, 34223240739004346, 37212896273420505, 33824163726741023,
    30199672860784225, 37943385296709364, 38798345742160872, 37212896282278091, 37943385296709364, 32862637875707057,
    32862637875707057, 33824163726741023, 33824163726741023, 38798345742160872, 33824163726741023, 34223240668649925,
    30199672860784225, 44004566681359755, 47267035222042548, 38437611719706268, 51083552702548408, 33755787679987563,
    34492753273898912, 39428213021704010, 34492753273898912, 33755787679987563, 43429979947878199, 39465445927903047,
    47267035273762788, 39428213021704010, 34492753273898912, 39465445927903047, 34492753273898912, 39428213021704010,
    34492753273898912, 44004566681359755, 49190577020930600, 36718590899829556, 52267325797748966, 40215016725837636,
    36718590899829556, 53267325450850874, 36718590899829556, 36718590899829556, 42092139686839915, 34759232884490278,
    40215016725837636, 42092139686839915, 49190577103092091, 36718590899829556
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
noncomputable def negativeCeiling : ℝ := 117921345753 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5434041869233359715041280, coefficient := (-5434041869233359715041280) }, { argument := 6696423078876526086885212160, coefficient := (-6696423078876526086885212160) }, { argument := 262071869018781992960959447040, coefficient := (-262071869018781992960959447040) }, { argument := 262071965137847832033791836160, coefficient := (-262071965137847832033791836160) }, { argument := 6696519197942365159717601280, coefficient := (-6696519197942365159717601280) }, { argument := 22140056515601048158341169152, coefficient := (-22140056515601048158341169152) }, { argument := 104709806787919739124449280, coefficient := (-104709806787919739124449280) }, { argument := 5434041869233359715041280, coefficient := (-5434041869233359715041280) }, { argument := 79653682009116061822166761472, coefficient := (-79653682009116061822166761472) }, { argument := 168664299556589280386088960, coefficient := (-168664299556589280386088960) }, { argument := 22145702928298953176902533120, coefficient := (-22145702928298953176902533120) }, { argument := 168664299556589280386088960, coefficient := (-168664299556589280386088960) }, { argument := 175770354308663673859604480, coefficient := (-175770354308663673859604480) }, { argument := 104709806787919739124449280, coefficient := (-104709806787919739124449280) }, { argument := 5225040258878230495232000, coefficient := (-5225040258878230495232000) }, { argument := 23121805900167723251165822976, coefficient := (-23121805900167723251165822976) }, { argument := 183652880184034267321511968768, coefficient := (-183652880184034267321511968768) }, { argument := 17534266358430645106579079168, coefficient := (-17534266358430645106579079168) }, { argument := 22747156356882999057183670272, coefficient := (-22747156356882999057183670272) }, { argument := 304717115364078508203522916352, coefficient := (-304717115364078508203522916352) }, { argument := 551144642563644331323012677632, coefficient := (-551144642563644331323012677632) }, { argument := 183652881311591498827008311296, coefficient := (-183652881311591498827008311296) }, { argument := 304717115364078508203522916352, coefficient := (-304717115364078508203522916352) }, { argument := 18008165449199040920270405632, coefficient := (-18008165449199040920270405632) }, { argument := 18008165449199040920270405632, coefficient := (-18008165449199040920270405632) }, { argument := 17534266358430645106579079168, coefficient := (-17534266358430645106579079168) }, { argument := 17534266358430645106579079168, coefficient := (-17534266358430645106579079168) }, { argument := 551144642563644331323012677632, coefficient := (-551144642563644331323012677632) }, { argument := 17534266358430645106579079168, coefficient := (-17534266358430645106579079168) }, { argument := 23121804772610491745669480448, coefficient := (-23121804772610491745669480448) }, { argument := 22747156356882999057183670272, coefficient := (-22747156356882999057183670272) }, { argument := 79479347276433321582363934720, coefficient := (-79479347276433321582363934720) }, { argument := 3050810088079191302960131866624, coefficient := (-3050810088079191302960131866624) }, { argument := 1716855802011305042443772100608, coefficient := (-1716855802011305042443772100608) }, { argument := 21491732119921621351818007150592, coefficient := (-21491732119921621351818007150592) }, { argument := 1070247772682371974510403387392, coefficient := (-1070247772682371974510403387392) }, { argument := 55742071493873540339083509760, coefficient := (-55742071493873540339083509760) }, { argument := 1705707387712530334375955398656, coefficient := (-1705707387712530334375955398656) }, { argument := 1783746287803953290850672312320, coefficient := (-1783746287803953290850672312320) }, { argument := 1070247772682371974510403387392, coefficient := (-1070247772682371974510403387392) }, { argument := 27324763446296809474218736484352, coefficient := (-27324763446296809474218736484352) }, { argument := 1750301044907629166647222206464, coefficient := (-1750301044907629166647222206464) }, { argument := 3050810197449936915984063397888, coefficient := (-3050810197449936915984063397888) }, { argument := 1705707387712530334375955398656, coefficient := (-1705707387712530334375955398656) }, { argument := 55742071493873540339083509760, coefficient := (-55742071493873540339083509760) }, { argument := 1750301044907629166647222206464, coefficient := (-1750301044907629166647222206464) }, { argument := 55742071493873540339083509760, coefficient := (-55742071493873540339083509760) }, { argument := 1705707387712530334375955398656, coefficient := (-1705707387712530334375955398656) }, { argument := 1783746287803953290850672312320, coefficient := (-1783746287803953290850672312320) }, { argument := 79479347276433321582363934720, coefficient := (-79479347276433321582363934720) }, { argument := 1446668303522485179724897189888, coefficient := (-1446668303522485179724897189888) }, { argument := 260751607713901479142516326400, coefficient := (-260751607713901479142516326400) }, { argument := 48822793902507629016791451172864, coefficient := (-48822793902507629016791451172864) }, { argument := 2942768144199745264608398540800, coefficient := (-2942768144199745264608398540800) }, { argument := 260751607713901479142516326400, coefficient := (-260751607713901479142516326400) }, { argument := 48822782162998209816556143116288, coefficient := (-48822782162998209816556143116288) }, { argument := 260751607713901479142516326400, coefficient := (-260751607713901479142516326400) }, { argument := 260751607713901479142516326400, coefficient := (-260751607713901479142516326400) }, { argument := 10810016651224887035308319703040, coefficient := (-10810016651224887035308319703040) }, { argument := 268201653648584378546588221440, coefficient := (-268201653648584378546588221440) }, { argument := 2942768144199745264608398540800, coefficient := (-2942768144199745264608398540800) }, { argument := 10810016651224887035308319703040, coefficient := (-10810016651224887035308319703040) }, { argument := 1446668385910255898930182094848, coefficient := (-1446668385910255898930182094848) }, { argument := 260751607713901479142516326400, coefficient := (-260751607713901479142516326400) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4
