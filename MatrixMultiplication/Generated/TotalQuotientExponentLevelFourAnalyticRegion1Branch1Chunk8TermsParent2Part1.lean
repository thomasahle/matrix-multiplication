import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 8, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8

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
def constantNumerator : ℤ := (-622969491186783249506993187061760)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    86759, 708689, 2468035, 1844431, 1948365, 1260001,
    33747399, 60028245, 1818845, 33747399, 243645, 987373,
    1948365, 1922779, 60028245, 1922779, 2468035, 1260001,
    226521581, 7727921885, 152651992345, 241497645, 226521581, 375274767,
    1498904463, 746891859, 1498904463, 4496705411597, 58292535, 169440805166619,
    12449028473, 612199749, 6219411107, 12541548943, 564251732219, 58292535,
    612199749, 83040817666587, 15247453860111845, 59045, 38185, 1022735,
    1819405, 3811860458683425, 1022735, 7385, 29925, 59045,
    58275, 1819405, 58275, 20759981147103, 38185, 86759,
    129667, 273951, 708689, 1186335, 16886403, 511595,
    1186335, 548373, 277723, 273951
  ]
def negativeCoefficients : Array ℕ := #[
    6555324698996600785520820224, 6693378360756811993698009088, 11654965762549184824984207360, 8710079134365742591142526976, 9200893572396316296782807040, 11900372981564471677804347392,
    159367585921628582015039176704, 283475372213487365950820843520, 8589252665535039848704901120, 159367585921628582015039176704, 9204647853750197664727695360, 9325474322580900407165321216,
    9200893572396316296782807040, 9080067103565613554345181184, 283475372213487365950820843520, 9080067103565613554345181184, 11654965762549184824984207360, 11900372981564471677804347392,
    522323203984883520857178112, 71277498617107048533411758080, 703983058782521147259753594880, 71277524027497010068319109120, 522323203984883520857178112, 6922597584169982808368873472,
    6912476754975511970737815552, 6888861486855080016265347072, 6912476754975511970737815552, 10125680408031571021247021056, 68819678371376423514239139840, 381546773504871070901062336512,
    57411010551938554699911790592, 2823273022948056249554436096, 57363942490007806006270099456, 57837685909855885289662185472, 10164655563858581168372842496, 68819678371376423514239139840,
    2823273022948056249554436096, 23373912218736407146578051072, 4291776720171783499102363320320, 278832128981038201642680320, 360647128296754804969963520, 4829729484857686597629378560,
    8591897190765446850024570880, 4291773335328750198395712307200, 4829729484857686597629378560, 278997411807938639225159680, 282633633999748266039705600, 278832128981038201642680320,
    275195906789228574828134400, 8591897190765446850024570880, 275195906789228574828134400, 23373660839577898226414518272, 360647128296754804969963520, 6555324698996600785520820224,
    4898680757874066287394553856, 5174788081394488703748931584, 6693378360756811993698009088, 89636938263282568873440706560, 159487567086858851090983550976, 4831878161607392286201610240,
    89636938263282568873440706560, 5179236550621351909540233216, 5246039146888025910733176832, 5174788081394488703748931584
  ]
def negativeScales : Array ℕ := #[
    16, 19, 21, 20, 20, 20,
    25, 25, 20, 25, 17, 19,
    20, 20, 25, 20, 21, 20,
    27, 32, 37, 27, 27, 28,
    30, 29, 30, 42, 25, 47,
    33, 29, 32, 33, 39, 25,
    29, 46, 53, 15, 15, 19,
    20, 51, 19, 12, 14, 15,
    15, 20, 15, 44, 15, 16,
    16, 18, 19, 20, 24, 18,
    20, 19, 18, 18
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16404725803890267, 19434793130685921, 21234931423280060, 20814744389142979, 20893832545500574, 20264993448044976,
    25008272978392689, 25839138155224452, 20794591173222159, 25008272978392689, 17894421094723376, 19913235674669191,
    20893832545500574, 20874761524086105, 25839138155224452, 20874761524086105, 21234931423280060, 20264993448044976,
    27755073263566388, 32847433366903754, 37151455462833972, 27847433881223686, 27755073263566388, 28483372047597849,
    30481261285872212, 29476324132262948, 30481261285872212, 42032005511837141, 25796807807109769, 47267774678432110,
    33535314107081486, 29189427212463429, 32534130837360343, 33545996487954447, 39037547986172205, 25796807807109769,
    29189427212463429, 46238885882888085, 53759417868685508, 15849527276949092, 15220718403268574, 19964000960516755,
    20795035292916470, 51759416730858792, 19964000960516755, 12850382207396955, 14869063629199677, 15849527276949092,
    15830589480093830, 20795035292916470, 15830589480093830, 44238870367068048, 15220718403268574, 16404725803890267,
    16984451856087507, 18063558344342460, 19434793130685921, 20178080028275706, 24009358714273789, 18964642652073247,
    20178080028275706, 19064798013961977, 18083287135251826, 18063558344342460
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
noncomputable def negativeCeiling : ℝ := 6605322673 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 6555324698996600785520820224, coefficient := (-6555324698996600785520820224) }, { argument := 6693378360756811993698009088, coefficient := (-6693378360756811993698009088) }, { argument := 11654965762549184824984207360, coefficient := (-11654965762549184824984207360) }, { argument := 8710079134365742591142526976, coefficient := (-8710079134365742591142526976) }, { argument := 9200893572396316296782807040, coefficient := (-9200893572396316296782807040) }, { argument := 11900372981564471677804347392, coefficient := (-11900372981564471677804347392) }, { argument := 159367585921628582015039176704, coefficient := (-159367585921628582015039176704) }, { argument := 283475372213487365950820843520, coefficient := (-283475372213487365950820843520) }, { argument := 8589252665535039848704901120, coefficient := (-8589252665535039848704901120) }, { argument := 159367585921628582015039176704, coefficient := (-159367585921628582015039176704) }, { argument := 9204647853750197664727695360, coefficient := (-9204647853750197664727695360) }, { argument := 9325474322580900407165321216, coefficient := (-9325474322580900407165321216) }, { argument := 9200893572396316296782807040, coefficient := (-9200893572396316296782807040) }, { argument := 9080067103565613554345181184, coefficient := (-9080067103565613554345181184) }, { argument := 283475372213487365950820843520, coefficient := (-283475372213487365950820843520) }, { argument := 9080067103565613554345181184, coefficient := (-9080067103565613554345181184) }, { argument := 11654965762549184824984207360, coefficient := (-11654965762549184824984207360) }, { argument := 11900372981564471677804347392, coefficient := (-11900372981564471677804347392) }, { argument := 522323203984883520857178112, coefficient := (-522323203984883520857178112) }, { argument := 71277498617107048533411758080, coefficient := (-71277498617107048533411758080) }, { argument := 703983058782521147259753594880, coefficient := (-703983058782521147259753594880) }, { argument := 71277524027497010068319109120, coefficient := (-71277524027497010068319109120) }, { argument := 522323203984883520857178112, coefficient := (-522323203984883520857178112) }, { argument := 6922597584169982808368873472, coefficient := (-6922597584169982808368873472) }, { argument := 6912476754975511970737815552, coefficient := (-6912476754975511970737815552) }, { argument := 6888861486855080016265347072, coefficient := (-6888861486855080016265347072) }, { argument := 6912476754975511970737815552, coefficient := (-6912476754975511970737815552) }, { argument := 10125680408031571021247021056, coefficient := (-10125680408031571021247021056) }, { argument := 68819678371376423514239139840, coefficient := (-68819678371376423514239139840) }, { argument := 381546773504871070901062336512, coefficient := (-381546773504871070901062336512) }, { argument := 57411010551938554699911790592, coefficient := (-57411010551938554699911790592) }, { argument := 2823273022948056249554436096, coefficient := (-2823273022948056249554436096) }, { argument := 57363942490007806006270099456, coefficient := (-57363942490007806006270099456) }, { argument := 57837685909855885289662185472, coefficient := (-57837685909855885289662185472) }, { argument := 10164655563858581168372842496, coefficient := (-10164655563858581168372842496) }, { argument := 68819678371376423514239139840, coefficient := (-68819678371376423514239139840) }, { argument := 2823273022948056249554436096, coefficient := (-2823273022948056249554436096) }, { argument := 23373912218736407146578051072, coefficient := (-23373912218736407146578051072) }, { argument := 4291776720171783499102363320320, coefficient := (-4291776720171783499102363320320) }, { argument := 278832128981038201642680320, coefficient := (-278832128981038201642680320) }, { argument := 360647128296754804969963520, coefficient := (-360647128296754804969963520) }, { argument := 4829729484857686597629378560, coefficient := (-4829729484857686597629378560) }, { argument := 8591897190765446850024570880, coefficient := (-8591897190765446850024570880) }, { argument := 4291773335328750198395712307200, coefficient := (-4291773335328750198395712307200) }, { argument := 4829729484857686597629378560, coefficient := (-4829729484857686597629378560) }, { argument := 278997411807938639225159680, coefficient := (-278997411807938639225159680) }, { argument := 282633633999748266039705600, coefficient := (-282633633999748266039705600) }, { argument := 278832128981038201642680320, coefficient := (-278832128981038201642680320) }, { argument := 275195906789228574828134400, coefficient := (-275195906789228574828134400) }, { argument := 8591897190765446850024570880, coefficient := (-8591897190765446850024570880) }, { argument := 275195906789228574828134400, coefficient := (-275195906789228574828134400) }, { argument := 23373660839577898226414518272, coefficient := (-23373660839577898226414518272) }, { argument := 360647128296754804969963520, coefficient := (-360647128296754804969963520) }, { argument := 6555324698996600785520820224, coefficient := (-6555324698996600785520820224) }, { argument := 4898680757874066287394553856, coefficient := (-4898680757874066287394553856) }, { argument := 5174788081394488703748931584, coefficient := (-5174788081394488703748931584) }, { argument := 6693378360756811993698009088, coefficient := (-6693378360756811993698009088) }, { argument := 89636938263282568873440706560, coefficient := (-89636938263282568873440706560) }, { argument := 159487567086858851090983550976, coefficient := (-159487567086858851090983550976) }, { argument := 4831878161607392286201610240, coefficient := (-4831878161607392286201610240) }, { argument := 89636938263282568873440706560, coefficient := (-89636938263282568873440706560) }, { argument := 5179236550621351909540233216, coefficient := (-5179236550621351909540233216) }, { argument := 5246039146888025910733176832, coefficient := (-5246039146888025910733176832) }, { argument := 5174788081394488703748931584, coefficient := (-5174788081394488703748931584) }] }

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
def constantNumerator : ℤ := (-340609923254225658397469513351168)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    540829, 16886403, 540829, 86759, 708689, 628239610077,
    340514046248087, 3585801163092927, 170257473241627, 628239610077, 80125, 59881,
    63255, 20453, 1095609, 1948605, 59045, 1095609,
    31635, 32053, 63255, 62419, 1948605, 62419,
    80125, 20453, 94310059, 12893632087, 509622456553, 51574546531,
    94310059, 388648335, 15209965361, 15209968241, 388651215, 40603,
    30343, 32053, 20729, 555199, 987677, 29925,
    555199, 4009, 16245, 32053, 31635, 987677,
    31635, 40603, 20729, 40075, 29947, 31635,
    40919, 547983, 243765, 7385, 547983, 31665,
    4009, 31635, 7807, 243765
  ]
def negativeCoefficients : Array ℕ := #[
    5107985485127814702555987968, 159487567086858851090983550976, 5107985485127814702555987968, 6555324698996600785520820224, 6693378360756811993698009088, 1414669836921081451927044096,
    383384732949326113685570060288, 4037253195482499297814876520448, 383385746524016775439629418496, 1414669836921081451927044096, 378379614439930322747392000, 282780027360717225041330176,
    298713291873919407992340480, 386346246696531414222897152, 5173867219930329122932260864, 9202026940352205011634094080, 278832128981038201642680320, 5173867219930329122932260864,
    298784127371162452670545920, 302732025750841476069195776, 298713291873919407992340480, 294765393494240384593690624, 9202026940352205011634094080, 294765393494240384593690624,
    378379614439930322747392000, 386346246696531414222897152, 434928380487362040442126336, 59461382822364641958610075648, 587554689390522262372879433728, 59461403785936360224908640256,
    434928380487362040442126336, 7169296370418334509154959360, 280574338384354310854201573376, 280574391510977243137710227456, 7169349497041266792663613440, 383484492607912409223397376,
    286581532379427289438355456, 302732025750841476069195776, 391559739293619502538817536, 5243706297845488305997611008, 9328345521402485151455248384, 282633633999748266039705600,
    5243706297845488305997611008, 302911475677190522587316224, 306859374056869545985966080, 302732025750841476069195776, 298784127371162452670545920, 9328345521402485151455248384,
    298784127371162452670545920, 383484492607912409223397376, 391559739293619502538817536, 378497673602002063877734400, 282841418124994530429108224, 298784127371162452670545920,
    386469028225086024998453248, 5175553104764713586273550336, 9209181325573752524132843520, 278997411807938639225159680, 5175553104764713586273550336, 299067469360134631383367680,
    302911475677190522587316224, 298784127371162452670545920, 294940121054106561466597376, 9209181325573752524132843520
  ]
def negativeScales : Array ℕ := #[
    19, 24, 19, 16, 19, 39,
    48, 51, 47, 39, 16, 15,
    15, 14, 20, 20, 15, 20,
    14, 14, 15, 15, 20, 15,
    16, 14, 26, 33, 38, 35,
    26, 28, 33, 33, 28, 15,
    14, 14, 14, 19, 19, 14,
    19, 11, 13, 14, 14, 19,
    14, 15, 14, 15, 14, 14,
    15, 19, 17, 12, 19, 14,
    11, 14, 12, 17
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19044812987437190, 24009358714273789, 19044812987437190, 16404725803890267, 19434793130685921, 39192523950552415,
    48274707639243377, 51671216914627955, 47274711453368252, 39192523950552415, 16289964831280829, 15869810696364371,
    15948891912118346, 14320024849498394, 20063301591705037, 20894010246039576, 15849527276949092, 20063301591705037,
    14949233985692235, 14968171785853172, 15948891912118346, 15929697631284590, 20894010246039576, 15929697631284590,
    16289964831280829, 14320024849498394, 26490908319475509, 33585939671521184, 38890637898913743, 35585940180154421,
    26490908319475509, 28533890094733216, 33824297817414483, 33824298090588110, 28533900785493858, 15309298706103397,
    14889076114440872, 14968171785853172, 14339362899767194, 19082645443836523, 19913679794401665, 14869063629199677,
    19082645443836523, 11969026716473715, 13987708142652924, 14968171785853172, 14949233985692235, 19913679794401665,
    14949233985692235, 15309298706103397, 14339362899767194, 15290414899929273, 14870123867501686, 14949233985692235,
    15320483267724837, 19063771611790276, 17895131475802240, 12850382207396955, 19063771611790276, 14950601469486097,
    11969026716473715, 14949233985692235, 12930552561813914, 17895131475802240
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
noncomputable def negativeCeiling : ℝ := 224069163 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5107985485127814702555987968, coefficient := (-5107985485127814702555987968) }, { argument := 159487567086858851090983550976, coefficient := (-159487567086858851090983550976) }, { argument := 5107985485127814702555987968, coefficient := (-5107985485127814702555987968) }, { argument := 6555324698996600785520820224, coefficient := (-6555324698996600785520820224) }, { argument := 6693378360756811993698009088, coefficient := (-6693378360756811993698009088) }, { argument := 1414669836921081451927044096, coefficient := (-1414669836921081451927044096) }, { argument := 383384732949326113685570060288, coefficient := (-383384732949326113685570060288) }, { argument := 4037253195482499297814876520448, coefficient := (-4037253195482499297814876520448) }, { argument := 383385746524016775439629418496, coefficient := (-383385746524016775439629418496) }, { argument := 1414669836921081451927044096, coefficient := (-1414669836921081451927044096) }, { argument := 378379614439930322747392000, coefficient := (-378379614439930322747392000) }, { argument := 282780027360717225041330176, coefficient := (-282780027360717225041330176) }, { argument := 298713291873919407992340480, coefficient := (-298713291873919407992340480) }, { argument := 386346246696531414222897152, coefficient := (-386346246696531414222897152) }, { argument := 5173867219930329122932260864, coefficient := (-5173867219930329122932260864) }, { argument := 9202026940352205011634094080, coefficient := (-9202026940352205011634094080) }, { argument := 278832128981038201642680320, coefficient := (-278832128981038201642680320) }, { argument := 5173867219930329122932260864, coefficient := (-5173867219930329122932260864) }, { argument := 298784127371162452670545920, coefficient := (-298784127371162452670545920) }, { argument := 302732025750841476069195776, coefficient := (-302732025750841476069195776) }, { argument := 298713291873919407992340480, coefficient := (-298713291873919407992340480) }, { argument := 294765393494240384593690624, coefficient := (-294765393494240384593690624) }, { argument := 9202026940352205011634094080, coefficient := (-9202026940352205011634094080) }, { argument := 294765393494240384593690624, coefficient := (-294765393494240384593690624) }, { argument := 378379614439930322747392000, coefficient := (-378379614439930322747392000) }, { argument := 386346246696531414222897152, coefficient := (-386346246696531414222897152) }, { argument := 434928380487362040442126336, coefficient := (-434928380487362040442126336) }, { argument := 59461382822364641958610075648, coefficient := (-59461382822364641958610075648) }, { argument := 587554689390522262372879433728, coefficient := (-587554689390522262372879433728) }, { argument := 59461403785936360224908640256, coefficient := (-59461403785936360224908640256) }, { argument := 434928380487362040442126336, coefficient := (-434928380487362040442126336) }, { argument := 7169296370418334509154959360, coefficient := (-7169296370418334509154959360) }, { argument := 280574338384354310854201573376, coefficient := (-280574338384354310854201573376) }, { argument := 280574391510977243137710227456, coefficient := (-280574391510977243137710227456) }, { argument := 7169349497041266792663613440, coefficient := (-7169349497041266792663613440) }, { argument := 383484492607912409223397376, coefficient := (-383484492607912409223397376) }, { argument := 286581532379427289438355456, coefficient := (-286581532379427289438355456) }, { argument := 302732025750841476069195776, coefficient := (-302732025750841476069195776) }, { argument := 391559739293619502538817536, coefficient := (-391559739293619502538817536) }, { argument := 5243706297845488305997611008, coefficient := (-5243706297845488305997611008) }, { argument := 9328345521402485151455248384, coefficient := (-9328345521402485151455248384) }, { argument := 282633633999748266039705600, coefficient := (-282633633999748266039705600) }, { argument := 5243706297845488305997611008, coefficient := (-5243706297845488305997611008) }, { argument := 302911475677190522587316224, coefficient := (-302911475677190522587316224) }, { argument := 306859374056869545985966080, coefficient := (-306859374056869545985966080) }, { argument := 302732025750841476069195776, coefficient := (-302732025750841476069195776) }, { argument := 298784127371162452670545920, coefficient := (-298784127371162452670545920) }, { argument := 9328345521402485151455248384, coefficient := (-9328345521402485151455248384) }, { argument := 298784127371162452670545920, coefficient := (-298784127371162452670545920) }, { argument := 383484492607912409223397376, coefficient := (-383484492607912409223397376) }, { argument := 391559739293619502538817536, coefficient := (-391559739293619502538817536) }, { argument := 378497673602002063877734400, coefficient := (-378497673602002063877734400) }, { argument := 282841418124994530429108224, coefficient := (-282841418124994530429108224) }, { argument := 298784127371162452670545920, coefficient := (-298784127371162452670545920) }, { argument := 386469028225086024998453248, coefficient := (-386469028225086024998453248) }, { argument := 5175553104764713586273550336, coefficient := (-5175553104764713586273550336) }, { argument := 9209181325573752524132843520, coefficient := (-9209181325573752524132843520) }, { argument := 278997411807938639225159680, coefficient := (-278997411807938639225159680) }, { argument := 5175553104764713586273550336, coefficient := (-5175553104764713586273550336) }, { argument := 299067469360134631383367680, coefficient := (-299067469360134631383367680) }, { argument := 302911475677190522587316224, coefficient := (-302911475677190522587316224) }, { argument := 298784127371162452670545920, coefficient := (-298784127371162452670545920) }, { argument := 294940121054106561466597376, coefficient := (-294940121054106561466597376) }, { argument := 9209181325573752524132843520, coefficient := (-9209181325573752524132843520) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8
