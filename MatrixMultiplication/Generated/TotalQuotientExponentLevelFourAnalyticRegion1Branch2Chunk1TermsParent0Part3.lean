import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 1, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-46460294362713489455738829930496)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1556438787, 272127795, 6564075, 6564075, 2813175, 6564075,
    74080275, 2813175, 44522169, 5813895, 44530073, 3206013685,
    477140139, 14597408595, 489614391, 15592815, 477140139, 271314981,
    489614391, 7643597913, 9355689, 1603007875, 477140139, 15592815,
    9355689, 15592815, 240129351, 271314981, 44530073, 225676705,
    67475973, 795222541, 1669671417, 53119383, 397611459, 27277521,
    27277521, 923128737, 50248065, 1669671417, 923128737, 225675951,
    53119383, 50248065, 67475973, 22867987, 2397667193, 25844455875,
    1198834511, 22867987, 3385736457, 59246167323, 59246196381, 3385707399,
    207042325, 5663133895, 1656338065, 20273871, 354767469, 354767643,
    20273697, 189240555, 5176210233, 1513923951
  ]
def negativeCoefficients : Array ℕ := #[
    7177806992545983276880232448, 5019871789707897751700766720, 121085811605635025023795200, 121085811605635025023795200, 103787838519115735734681600, 121085811605635025023795200,
    1366539873835023853839974400, 103787838519115735734681600, 205322264287361278490443776, 107247433136419593592504320, 205358715053650928564436992, 14785128486001367799027466240,
    2200420507856800425921478656, 134637330245666561146497269760, 2257947841395540306337726464, 71909166923424850520309760, 2200420507856800425921478656, 1251219504467592399053389824,
    2257947841395540306337726464, 35249873625862861725055844352, 1380656004929757129989947392, 14785138009132995851583488000, 2200420507856800425921478656, 71909166923424850520309760,
    1380656004929757129989947392, 71909166923424850520309760, 2214802341241485396025540608, 1251219504467592399053389824, 205358715053650928564436992, 520375052566631091965788160,
    311178001263883928670830592, 7334633347736000466023088128, 7700000329146744873280339968, 244969915888589475762143232, 7334636824947258360273567744, 251590724426118921053011968,
    251590724426118921053011968, 4257179889631433322028597248, 231728298813530585180405760, 7700000329146744873280339968, 4257179889631433322028597248, 520373313961002144840548352,
    244969915888589475762143232, 231728298813530585180405760, 311178001263883928670830592, 105459975917479267032629248, 11057288270800141430105833472, 119186515812601063576436736000,
    11057296705573869133798309888, 105459975917479267032629248, 3903488370206695258463404032, 136612360744444342543105130496, 136612427747630504274623987712, 3903454868613614392703975424,
    3819256781700796941284147200, 13058297702026867517727703040, 3819255548074787011957882880, 186993454860200970465312768, 6544304706320687067933179904, 6544307916054155893395161088,
    186991849993466557734322176, 3490872086451756456612986880, 11935528179983435918072610816, 3490870958894524951116644352
  ]
def negativeScales : Array ℕ := #[
    30, 28, 22, 22, 21, 22,
    26, 21, 25, 22, 25, 31,
    28, 33, 28, 23, 28, 28,
    28, 32, 23, 30, 28, 23,
    23, 23, 27, 28, 25, 27,
    26, 29, 30, 25, 28, 24,
    24, 29, 25, 30, 29, 27,
    25, 25, 26, 24, 31, 34,
    30, 24, 31, 35, 35, 31,
    27, 32, 30, 24, 28, 28,
    24, 27, 32, 30
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30535601692324491, 28019709079378918, 22646160292276457, 22646160292276457, 21423767870920709, 22646160292276457,
    26142586118376639, 21423767870920709, 25408020542815031, 22471073585699149, 25408276641064262, 31578133437697462,
    28829837817167079, 33764993226579573, 28867070724584102, 23894378072136426, 28829837817167079, 28015393469150310,
    28867070724584102, 32831604743382534, 23157412474022738, 30578134366940002, 28829837817167079, 23894378072136426,
    23157412474022738, 23894378072136426, 27839236515404896, 28015393469150310, 25408276641064262, 27749682266396706,
    26007870539640660, 29566783410528477, 30636917069451459, 25662735053621334, 28566784094482808, 24701209201481082,
    24701209201481082, 29781956615736132, 25582564704911453, 30636917069451459, 29781956615736132, 27749677446254178,
    25662735053621334, 25582564704911453, 26007870539640660, 24446826039452413, 31158984274068816, 34589135777213169,
    30158985374591954, 24446826039452413, 31656822533395024, 35786002777411928, 35786003484999009, 31656810151447122,
    27625350482515018, 32398953494242435, 30625350016522151, 24273118240895651, 28402298484453560, 28402299192040634,
    24273105858947757, 27495646056167742, 32269249067906154, 30495645590174876
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
noncomputable def negativeCeiling : ℝ := 151957761 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7177806992545983276880232448, coefficient := (-7177806992545983276880232448) }, { argument := 5019871789707897751700766720, coefficient := (-5019871789707897751700766720) }, { argument := 121085811605635025023795200, coefficient := (-121085811605635025023795200) }, { argument := 121085811605635025023795200, coefficient := (-121085811605635025023795200) }, { argument := 103787838519115735734681600, coefficient := (-103787838519115735734681600) }, { argument := 121085811605635025023795200, coefficient := (-121085811605635025023795200) }, { argument := 1366539873835023853839974400, coefficient := (-1366539873835023853839974400) }, { argument := 103787838519115735734681600, coefficient := (-103787838519115735734681600) }, { argument := 205322264287361278490443776, coefficient := (-205322264287361278490443776) }, { argument := 107247433136419593592504320, coefficient := (-107247433136419593592504320) }, { argument := 205358715053650928564436992, coefficient := (-205358715053650928564436992) }, { argument := 14785128486001367799027466240, coefficient := (-14785128486001367799027466240) }, { argument := 2200420507856800425921478656, coefficient := (-2200420507856800425921478656) }, { argument := 134637330245666561146497269760, coefficient := (-134637330245666561146497269760) }, { argument := 2257947841395540306337726464, coefficient := (-2257947841395540306337726464) }, { argument := 71909166923424850520309760, coefficient := (-71909166923424850520309760) }, { argument := 2200420507856800425921478656, coefficient := (-2200420507856800425921478656) }, { argument := 1251219504467592399053389824, coefficient := (-1251219504467592399053389824) }, { argument := 2257947841395540306337726464, coefficient := (-2257947841395540306337726464) }, { argument := 35249873625862861725055844352, coefficient := (-35249873625862861725055844352) }, { argument := 1380656004929757129989947392, coefficient := (-1380656004929757129989947392) }, { argument := 14785138009132995851583488000, coefficient := (-14785138009132995851583488000) }, { argument := 2200420507856800425921478656, coefficient := (-2200420507856800425921478656) }, { argument := 71909166923424850520309760, coefficient := (-71909166923424850520309760) }, { argument := 1380656004929757129989947392, coefficient := (-1380656004929757129989947392) }, { argument := 71909166923424850520309760, coefficient := (-71909166923424850520309760) }, { argument := 2214802341241485396025540608, coefficient := (-2214802341241485396025540608) }, { argument := 1251219504467592399053389824, coefficient := (-1251219504467592399053389824) }, { argument := 205358715053650928564436992, coefficient := (-205358715053650928564436992) }, { argument := 520375052566631091965788160, coefficient := (-520375052566631091965788160) }, { argument := 311178001263883928670830592, coefficient := (-311178001263883928670830592) }, { argument := 7334633347736000466023088128, coefficient := (-7334633347736000466023088128) }, { argument := 7700000329146744873280339968, coefficient := (-7700000329146744873280339968) }, { argument := 244969915888589475762143232, coefficient := (-244969915888589475762143232) }, { argument := 7334636824947258360273567744, coefficient := (-7334636824947258360273567744) }, { argument := 251590724426118921053011968, coefficient := (-251590724426118921053011968) }, { argument := 251590724426118921053011968, coefficient := (-251590724426118921053011968) }, { argument := 4257179889631433322028597248, coefficient := (-4257179889631433322028597248) }, { argument := 231728298813530585180405760, coefficient := (-231728298813530585180405760) }, { argument := 7700000329146744873280339968, coefficient := (-7700000329146744873280339968) }, { argument := 4257179889631433322028597248, coefficient := (-4257179889631433322028597248) }, { argument := 520373313961002144840548352, coefficient := (-520373313961002144840548352) }, { argument := 244969915888589475762143232, coefficient := (-244969915888589475762143232) }, { argument := 231728298813530585180405760, coefficient := (-231728298813530585180405760) }, { argument := 311178001263883928670830592, coefficient := (-311178001263883928670830592) }, { argument := 105459975917479267032629248, coefficient := (-105459975917479267032629248) }, { argument := 11057288270800141430105833472, coefficient := (-11057288270800141430105833472) }, { argument := 119186515812601063576436736000, coefficient := (-119186515812601063576436736000) }, { argument := 11057296705573869133798309888, coefficient := (-11057296705573869133798309888) }, { argument := 105459975917479267032629248, coefficient := (-105459975917479267032629248) }, { argument := 3903488370206695258463404032, coefficient := (-3903488370206695258463404032) }, { argument := 136612360744444342543105130496, coefficient := (-136612360744444342543105130496) }, { argument := 136612427747630504274623987712, coefficient := (-136612427747630504274623987712) }, { argument := 3903454868613614392703975424, coefficient := (-3903454868613614392703975424) }, { argument := 3819256781700796941284147200, coefficient := (-3819256781700796941284147200) }, { argument := 13058297702026867517727703040, coefficient := (-13058297702026867517727703040) }, { argument := 3819255548074787011957882880, coefficient := (-3819255548074787011957882880) }, { argument := 186993454860200970465312768, coefficient := (-186993454860200970465312768) }, { argument := 6544304706320687067933179904, coefficient := (-6544304706320687067933179904) }, { argument := 6544307916054155893395161088, coefficient := (-6544307916054155893395161088) }, { argument := 186991849993466557734322176, coefficient := (-186991849993466557734322176) }, { argument := 3490872086451756456612986880, coefficient := (-3490872086451756456612986880) }, { argument := 11935528179983435918072610816, coefficient := (-11935528179983435918072610816) }, { argument := 3490870958894524951116644352, coefficient := (-3490870958894524951116644352) }] }

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

end TermShard6


end Parent0

namespace Parent0

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 4403892735823047723856338442256384
def positiveArguments : Array ℕ := #[
    99, 386995, 10585297, 3095959, 7446085, 329,
    118521039, 8141, 259, 118521097, 133, 133,
    4501, 245, 8141, 4501, 7446027, 259,
    245, 329, 3017713, 196795283, 38097, 1682789505,
    39093, 1245, 38097, 21663, 39093, 610299,
    747, 98397701, 38097, 1245, 747, 1245,
    19173, 21663, 3017713, 92891605, 2134300203, 4165,
    3689, 172669, 47005, 1067150475, 172669, 4165,
    4165, 1785, 4165, 47005, 1785, 46445429,
    3689, 15988813, 14529, 148567987, 23403, 725
  ]
def positiveCoefficients : Array ℕ := #[
    62748704711297355374086808666112, 29240515472610213591588536320, 99975303528041213743201255424, 29240506027877247852298108928, 70326284465196844362047160320, 6363785514451407975653310464,
    2238799128353944209154507800576, 157469841559723137780527661056, 5009788596483023299982393344, 2238800223942968234912197378048, 5145188288279861767549485056, 5145188288279861767549485056,
    87062001825367134645639970816, 4738989212889346364848209920, 157469841559723137780527661056, 87062001825367134645639970816, 70325736670684831483202371584, 5009788596483023299982393344,
    4738989212889346364848209920, 6363785514451407975653310464, 57002986904480022667032788992, 3717357793704185927755599183872, 736903151197736442700498993152, 31786995024547204994724444241920,
    756168593059115173228616613888, 24081802326723413160147025920, 736903151197736442700498993152, 419023360484987388986558251008, 756168593059115173228616613888, 11804899500559817131104072105984,
    462370604673089532674822897664, 3717360041550631773706720903168, 736903151197736442700498993152, 24081802326723413160147025920, 462370604673089532674822897664, 24081802326723413160147025920,
    741719511663081125332528398336, 419023360484987388986558251008, 57002986904480022667032788992, 438668201991966349680789422080, 10078947743029079802129351180288, 322251266476475552809678274560,
    285422550307735489631429328896, 13359616790210457917909805039616, 3636835721663081238852083384320, 10078951270636842505754325811200, 13359616790210457917909805039616, 322251266476475552809678274560,
    322251266476475552809678274560, 276215371265550473836867092480, 322251266476475552809678274560, 3636835721663081238852083384320, 276215371265550473836867092480, 438664674384203646055814791168,
    285422550307735489631429328896, 75505034612070460698130382848, 562063463461790312937792995328, 1403184964472426345605999099904, 905359710606117330420756381696, 28047079015059396853183283200
  ]
def positiveScales : Array ℕ := #[
    6, 18, 23, 21, 22, 8,
    26, 12, 8, 26, 7, 7,
    12, 7, 12, 12, 22, 8,
    7, 8, 21, 27, 15, 30,
    15, 10, 15, 14, 15, 19,
    9, 26, 15, 10, 9, 10,
    14, 14, 21, 26, 30, 12,
    11, 17, 15, 29, 17, 12,
    12, 10, 12, 15, 10, 25,
    11, 23, 13, 27, 14, 9
  ]
def negativeArguments : Array ℕ := #[
    1, 65, 725, 725
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 5149830563427181943580356771840, 57440417822841644755319363993600, 57440417822841644755319363993600
  ]
def negativeScales : Array ℕ := #[
    0, 6, 9, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    6629356620078832, 18561955401215154, 23335558412953919, 21561954935222288, 22828050654470950, 8361943773735241,
    26820567937712946, 12990990302267154, 8016808287686553, 26820568643716644, 7055282435501189, 7055282435501189,
    12136029849385551, 7936637938489789, 12990990302267154, 12136029849385551, 22828039416802008, 8016808287686553,
    7936637938489789, 8361943773735241, 21525024174007347, 27552120400131327, 15217389774760732, 30648207579621931,
    15254622680959707, 10281930026955443, 15217389774760732, 14402945427916808, 15254622680959707, 19219156700934920,
    9544964432789165, 26552121272513303, 15217389774760732, 10281930026955443, 9544964432789165, 10281930026955443,
    14226788472762982, 14402945427916808, 21525024174007347, 26469044884370247, 30991115967457206, 12024100780252909,
    11849014073589620, 17397649567374687, 15520526606372375, 29991116472396944, 17397649567374687, 12024100780252909,
    12024100780252909, 10801708358875019, 12024100780252909, 15520526606372375, 10801708358875019, 25469033282702596,
    11849014073589620, 23930559501718677, 13826647788254566, 27146548040709652, 14514405858405324, 9501837184902278
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 6022367813028455, 9501837184902585, 9501837184902585
  ]

abbrev PositiveTerm := Fin 60
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 20146306307 / 500000000000
noncomputable def negativeCeiling : ℝ := 13512723757 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 62748704711297355374086808666112, coefficient := 62748704711297355374086808666112 }, { argument := 29240515472610213591588536320, coefficient := 29240515472610213591588536320 }, { argument := 99975303528041213743201255424, coefficient := 99975303528041213743201255424 }, { argument := 29240506027877247852298108928, coefficient := 29240506027877247852298108928 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 70326284465196844362047160320, coefficient := 70326284465196844362047160320 }, { argument := 6363785514451407975653310464, coefficient := 6363785514451407975653310464 }, { argument := 2238799128353944209154507800576, coefficient := 2238799128353944209154507800576 }, { argument := 157469841559723137780527661056, coefficient := 157469841559723137780527661056 }, { argument := 5009788596483023299982393344, coefficient := 5009788596483023299982393344 }, { argument := 2238800223942968234912197378048, coefficient := 2238800223942968234912197378048 }, { argument := 5145188288279861767549485056, coefficient := 5145188288279861767549485056 }, { argument := 5145188288279861767549485056, coefficient := 5145188288279861767549485056 }, { argument := 87062001825367134645639970816, coefficient := 87062001825367134645639970816 }, { argument := 4738989212889346364848209920, coefficient := 4738989212889346364848209920 }, { argument := 157469841559723137780527661056, coefficient := 157469841559723137780527661056 }, { argument := 87062001825367134645639970816, coefficient := 87062001825367134645639970816 }, { argument := 70325736670684831483202371584, coefficient := 70325736670684831483202371584 }, { argument := 5009788596483023299982393344, coefficient := 5009788596483023299982393344 }, { argument := 4738989212889346364848209920, coefficient := 4738989212889346364848209920 }, { argument := 6363785514451407975653310464, coefficient := 6363785514451407975653310464 }, { argument := 5149830563427181943580356771840, coefficient := (-5149830563427181943580356771840) }, { argument := 57002986904480022667032788992, coefficient := 57002986904480022667032788992 }, { argument := 3717357793704185927755599183872, coefficient := 3717357793704185927755599183872 }, { argument := 736903151197736442700498993152, coefficient := 736903151197736442700498993152 }, { argument := 31786995024547204994724444241920, coefficient := 31786995024547204994724444241920 }, { argument := 756168593059115173228616613888, coefficient := 756168593059115173228616613888 }, { argument := 24081802326723413160147025920, coefficient := 24081802326723413160147025920 }, { argument := 736903151197736442700498993152, coefficient := 736903151197736442700498993152 }, { argument := 419023360484987388986558251008, coefficient := 419023360484987388986558251008 }, { argument := 756168593059115173228616613888, coefficient := 756168593059115173228616613888 }, { argument := 11804899500559817131104072105984, coefficient := 11804899500559817131104072105984 }, { argument := 462370604673089532674822897664, coefficient := 462370604673089532674822897664 }, { argument := 3717360041550631773706720903168, coefficient := 3717360041550631773706720903168 }, { argument := 736903151197736442700498993152, coefficient := 736903151197736442700498993152 }, { argument := 24081802326723413160147025920, coefficient := 24081802326723413160147025920 }, { argument := 462370604673089532674822897664, coefficient := 462370604673089532674822897664 }, { argument := 24081802326723413160147025920, coefficient := 24081802326723413160147025920 }, { argument := 741719511663081125332528398336, coefficient := 741719511663081125332528398336 }, { argument := 419023360484987388986558251008, coefficient := 419023360484987388986558251008 }, { argument := 57002986904480022667032788992, coefficient := 57002986904480022667032788992 }, { argument := 57440417822841644755319363993600, coefficient := (-57440417822841644755319363993600) }, { argument := 438668201991966349680789422080, coefficient := 438668201991966349680789422080 }, { argument := 10078947743029079802129351180288, coefficient := 10078947743029079802129351180288 }, { argument := 322251266476475552809678274560, coefficient := 322251266476475552809678274560 }, { argument := 285422550307735489631429328896, coefficient := 285422550307735489631429328896 }, { argument := 13359616790210457917909805039616, coefficient := 13359616790210457917909805039616 }, { argument := 3636835721663081238852083384320, coefficient := 3636835721663081238852083384320 }, { argument := 10078951270636842505754325811200, coefficient := 10078951270636842505754325811200 }, { argument := 13359616790210457917909805039616, coefficient := 13359616790210457917909805039616 }, { argument := 322251266476475552809678274560, coefficient := 322251266476475552809678274560 }, { argument := 322251266476475552809678274560, coefficient := 322251266476475552809678274560 }, { argument := 276215371265550473836867092480, coefficient := 276215371265550473836867092480 }, { argument := 322251266476475552809678274560, coefficient := 322251266476475552809678274560 }, { argument := 3636835721663081238852083384320, coefficient := 3636835721663081238852083384320 }, { argument := 276215371265550473836867092480, coefficient := 276215371265550473836867092480 }, { argument := 438664674384203646055814791168, coefficient := 438664674384203646055814791168 }, { argument := 285422550307735489631429328896, coefficient := 285422550307735489631429328896 }, { argument := 57440417822841644755319363993600, coefficient := (-57440417822841644755319363993600) }, { argument := 75505034612070460698130382848, coefficient := 75505034612070460698130382848 }, { argument := 562063463461790312937792995328, coefficient := 562063463461790312937792995328 }, { argument := 1403184964472426345605999099904, coefficient := 1403184964472426345605999099904 }, { argument := 905359710606117330420756381696, coefficient := 905359710606117330420756381696 }, { argument := 28047079015059396853183283200, coefficient := 28047079015059396853183283200 }] }

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

end TermShard7


end Parent0

namespace Parent0

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-312110151550728619572792355979264)
def positiveArguments : Array ℕ := #[
    23403, 15631, 16226381, 14529, 87, 535,
    489, 535, 489
  ]
def positiveCoefficients : Array ℕ := #[
    905359710606117330420756381696, 604695023564680596154631585792, 76626917772672836572257714176, 562063463461790312937792995328, 26925195854457020979055951872, 41393620063604902941939466240,
    37834542450659434651604484096, 41393620063604902941939466240, 37834542450659434651604484096
  ]
def positiveScales : Array ℕ := #[
    14, 13, 23, 13, 6, 9,
    8, 9, 8
  ]
def negativeArguments : Array ℕ := #[
    65, 1
  ]
def negativeCoefficients : Array ℕ := #[
    5149830563427181943580356771840, 158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    6, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    14514405858405324, 13932122457405559, 23951837932346390, 13826647788254566, 6442943495848725, 9063395081288509,
    8933690654464738, 9063395081288509, 8933690654464738
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    6022367813028455, 0
  ]

abbrev PositiveTerm := Fin 9
abbrev NegativeTerm := Fin 2
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
noncomputable def positiveFloor : ℝ := 78895883 / 200000000000
noncomputable def negativeCeiling : ℝ := 186659769 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 905359710606117330420756381696, coefficient := 905359710606117330420756381696 }, { argument := 604695023564680596154631585792, coefficient := 604695023564680596154631585792 }, { argument := 76626917772672836572257714176, coefficient := 76626917772672836572257714176 }, { argument := 562063463461790312937792995328, coefficient := 562063463461790312937792995328 }, { argument := 26925195854457020979055951872, coefficient := 26925195854457020979055951872 }, { argument := 5149830563427181943580356771840, coefficient := (-5149830563427181943580356771840) }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end TermShard8


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk1
