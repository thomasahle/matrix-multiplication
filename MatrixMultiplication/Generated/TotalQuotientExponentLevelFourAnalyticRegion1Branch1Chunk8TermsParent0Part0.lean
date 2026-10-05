import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 8, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-256857347443048602088901537955840)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    12926842875, 51581542395, 25643970575, 51581542395, 83187906740471, 21477194761,
    2982675236409857, 71003409153, 3507448345, 35449592671, 72036727579, 10434818618785,
    21477194761, 3507448345, 22206853351467, 1411408232691669, 1431350911, 116041913,
    24871361017, 44956209809, 705701148835945, 24871361017, 734278057, 734643113,
    1431350911, 1430620799, 44956209809, 1430620799, 11103403646871, 116041913,
    2415, 7245, 15295, 39445, 33005, 923335,
    28175, 33005, 29785, 15295, 15295, 29785,
    923335, 29785, 2415, 39445, 11320072129, 5837541246921,
    46009425, 57419465469949, 1792575, 2987625, 91421325, 2987625,
    1792575, 1464533775, 93811425, 2918775119129, 91421325, 2987625,
    93811425, 2987625, 91421325, 2987625
  ]
def negativeCoefficients : Array ℕ := #[
    59614540549045198031683584000, 59469469467985265099821547520, 59130970278845421592143462400, 59469469467985265099821547520, 23415314112382298006252158976, 198092157588691289901407141888,
    839548442703914878044515336192, 163722714625784660484377542656, 8087625246496390603278909440, 163482390879796701187312451584, 166105384694668458216503902208, 23497122621619419876090183680,
    198092157588691289901407141888, 8087625246496390603278909440, 12501347059842253930264264704, 794552198852231352373349449728, 6600940983722004463740780544, 8562381883738677503571525632,
    114698907861358879160682938368, 207323924217653490844052750336, 794548857733123209757909319680, 114698907861358879160682938368, 6772519698209857171468845056, 6775886745512143228506210304,
    6600940983722004463740780544, 6597573936419718406703415296, 207323924217653490844052750336, 6597573936419718406703415296, 12501321131648110488667029504, 8562381883738677503571525632,
    182472240898083091057213440, 136854180673562318292910080, 144457190710982447086960640, 186273745916793155454238720, 2493787292273802244448583680, 4360326256460443863387996160,
    133052675654852253895884800, 2493787292273802244448583680, 140655685692272382689935360, 144457190710982447086960640, 144457190710982447086960640, 140655685692272382689935360,
    4360326256460443863387996160, 140655685692272382689935360, 182472240898083091057213440, 186273745916793155454238720, 203924290487886149306023936, 26289948584393316180286242816,
    1697448175907068173719961600, 258594283294275378387777224704, 1058149512253756783617638400, 55111953763216499146752000, 1686425785154424873890611200, 1763582520422927972696064000,
    1058149512253756783617638400, 27015879734728727881737830400, 1730515348164998073208012800, 26289989077775278942839635968, 1686425785154424873890611200, 55111953763216499146752000,
    1730515348164998073208012800, 55111953763216499146752000, 1686425785154424873890611200, 1763582520422927972696064000
  ]
def negativeScales : Array ℕ := #[
    33, 35, 34, 35, 46, 34,
    51, 36, 31, 35, 36, 43,
    34, 31, 44, 50, 30, 26,
    34, 35, 49, 34, 29, 29,
    30, 30, 35, 30, 43, 26,
    11, 12, 13, 15, 15, 19,
    14, 15, 14, 13, 13, 14,
    19, 14, 11, 15, 33, 42,
    25, 45, 20, 21, 26, 21,
    20, 30, 26, 41, 26, 21,
    26, 21, 26, 21
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33589650917394809, 35586135862220719, 34577900607298489, 35586135862220719, 46241439048516975, 34322086517211469,
    51405528324105310, 36047169244618405, 31707774711172402, 35045049999331237, 36068013594126976, 43246470756884091,
    34322086517211469, 31707774711172402, 44336070215081258, 50326056753625135, 30414730261548542, 26790070743908151,
    34533766406117671, 35387801358092243, 49326050687030505, 34533766406117671, 29451751246542395, 29452468323132271,
    30414730261548542, 30413994175317596, 35387801358092243, 30413994175317596, 43336067222882440, 26790070743908151,
    11237807473723136, 12822769975464802, 13900772490874059, 15267554817117188, 15010396977620064, 19816494649918742,
    14782127990393705, 15010396977620064, 14862298340817341, 13900772490874059, 13900772490874059, 14862298340817341,
    19816494649918742, 14862298340817341, 11237807473723136, 15267554817117188, 33398164099606948, 42408497977306743,
    25455426090771593, 45706605133871962, 20773602051171266, 21510567644964381, 26446027392769327, 21510567644964381,
    20773602051171266, 30447794318943517, 26483260298968415, 41408500199431908, 26446027392769327, 21510567644964381,
    26483260298968415, 21510567644964381, 26446027392769327, 21510567644964381
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
noncomputable def negativeCeiling : ℝ := 2471419709 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 59614540549045198031683584000, coefficient := (-59614540549045198031683584000) }, { argument := 59469469467985265099821547520, coefficient := (-59469469467985265099821547520) }, { argument := 59130970278845421592143462400, coefficient := (-59130970278845421592143462400) }, { argument := 59469469467985265099821547520, coefficient := (-59469469467985265099821547520) }, { argument := 23415314112382298006252158976, coefficient := (-23415314112382298006252158976) }, { argument := 198092157588691289901407141888, coefficient := (-198092157588691289901407141888) }, { argument := 839548442703914878044515336192, coefficient := (-839548442703914878044515336192) }, { argument := 163722714625784660484377542656, coefficient := (-163722714625784660484377542656) }, { argument := 8087625246496390603278909440, coefficient := (-8087625246496390603278909440) }, { argument := 163482390879796701187312451584, coefficient := (-163482390879796701187312451584) }, { argument := 166105384694668458216503902208, coefficient := (-166105384694668458216503902208) }, { argument := 23497122621619419876090183680, coefficient := (-23497122621619419876090183680) }, { argument := 198092157588691289901407141888, coefficient := (-198092157588691289901407141888) }, { argument := 8087625246496390603278909440, coefficient := (-8087625246496390603278909440) }, { argument := 12501347059842253930264264704, coefficient := (-12501347059842253930264264704) }, { argument := 794552198852231352373349449728, coefficient := (-794552198852231352373349449728) }, { argument := 6600940983722004463740780544, coefficient := (-6600940983722004463740780544) }, { argument := 8562381883738677503571525632, coefficient := (-8562381883738677503571525632) }, { argument := 114698907861358879160682938368, coefficient := (-114698907861358879160682938368) }, { argument := 207323924217653490844052750336, coefficient := (-207323924217653490844052750336) }, { argument := 794548857733123209757909319680, coefficient := (-794548857733123209757909319680) }, { argument := 114698907861358879160682938368, coefficient := (-114698907861358879160682938368) }, { argument := 6772519698209857171468845056, coefficient := (-6772519698209857171468845056) }, { argument := 6775886745512143228506210304, coefficient := (-6775886745512143228506210304) }, { argument := 6600940983722004463740780544, coefficient := (-6600940983722004463740780544) }, { argument := 6597573936419718406703415296, coefficient := (-6597573936419718406703415296) }, { argument := 207323924217653490844052750336, coefficient := (-207323924217653490844052750336) }, { argument := 6597573936419718406703415296, coefficient := (-6597573936419718406703415296) }, { argument := 12501321131648110488667029504, coefficient := (-12501321131648110488667029504) }, { argument := 8562381883738677503571525632, coefficient := (-8562381883738677503571525632) }, { argument := 182472240898083091057213440, coefficient := (-182472240898083091057213440) }, { argument := 136854180673562318292910080, coefficient := (-136854180673562318292910080) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 186273745916793155454238720, coefficient := (-186273745916793155454238720) }, { argument := 2493787292273802244448583680, coefficient := (-2493787292273802244448583680) }, { argument := 4360326256460443863387996160, coefficient := (-4360326256460443863387996160) }, { argument := 133052675654852253895884800, coefficient := (-133052675654852253895884800) }, { argument := 2493787292273802244448583680, coefficient := (-2493787292273802244448583680) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 4360326256460443863387996160, coefficient := (-4360326256460443863387996160) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 182472240898083091057213440, coefficient := (-182472240898083091057213440) }, { argument := 186273745916793155454238720, coefficient := (-186273745916793155454238720) }, { argument := 203924290487886149306023936, coefficient := (-203924290487886149306023936) }, { argument := 26289948584393316180286242816, coefficient := (-26289948584393316180286242816) }, { argument := 1697448175907068173719961600, coefficient := (-1697448175907068173719961600) }, { argument := 258594283294275378387777224704, coefficient := (-258594283294275378387777224704) }, { argument := 1058149512253756783617638400, coefficient := (-1058149512253756783617638400) }, { argument := 55111953763216499146752000, coefficient := (-55111953763216499146752000) }, { argument := 1686425785154424873890611200, coefficient := (-1686425785154424873890611200) }, { argument := 1763582520422927972696064000, coefficient := (-1763582520422927972696064000) }, { argument := 1058149512253756783617638400, coefficient := (-1058149512253756783617638400) }, { argument := 27015879734728727881737830400, coefficient := (-27015879734728727881737830400) }, { argument := 1730515348164998073208012800, coefficient := (-1730515348164998073208012800) }, { argument := 26289989077775278942839635968, coefficient := (-26289989077775278942839635968) }, { argument := 1686425785154424873890611200, coefficient := (-1686425785154424873890611200) }, { argument := 55111953763216499146752000, coefficient := (-55111953763216499146752000) }, { argument := 1730515348164998073208012800, coefficient := (-1730515348164998073208012800) }, { argument := 55111953763216499146752000, coefficient := (-55111953763216499146752000) }, { argument := 1686425785154424873890611200, coefficient := (-1686425785154424873890611200) }, { argument := 1763582520422927972696064000, coefficient := (-1763582520422927972696064000) }] }

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


end Parent0

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-8034809426944143691428630141861888)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    11320072129, 12926846981, 51581558789, 25643978737, 51581558789, 301760753479645,
    159323733187, 10756061925833419, 263352860811, 13009390529, 131482847663, 267192023387,
    37850316239531, 159323733187, 13009390529, 1719926394730591, 111105820909782945, 54956939649,
    4455954951, 955059398151, 1727396778351, 111105813016262505, 955059398151, 28220415063,
    28220768343, 54956939649, 54956233089, 1727396778351, 54956233089, 1719922711971991,
    4455954951, 27255, 81765, 172615, 445165, 372485,
    10420495, 317975, 372485, 336145, 172615, 172615,
    336145, 10420495, 336145, 27255, 445165, 5852512944397,
    112370450422959, 21752074575, 4560984071207201, 847483425, 1412472375, 43221654675,
    1412472375, 847483425, 692393958225, 44351632575, 224741225283211, 43221654675,
    1412472375, 44351632575, 1412472375, 43221654675
  ]
def negativeCoefficients : Array ℕ := #[
    203924290487886149306023936, 59614559484627989694538317824, 59469488368980411624470872064, 59130989099136062794313498624, 59469488368980411624470872064, 84938101057873082888350597120,
    734751032742143515750247170048, 3027562280072335336988018212864, 607250353057471333896208515072, 29997612205425489836253380608, 606357610230475254608640868352, 616102859244575770903444455424,
    85231335056103622510209138688, 734751032742143515750247170048, 29997612205425489836253380608, 484116241900835640164478877696, 31273508352999470873547028561920, 253444150194851058928840605696,
    328791442340303941837221003264, 4404434073220642587089257365504, 7966211570997820284793786466304, 31273506131170988859459926753280, 4404434073220642587089257365504, 260287387160509506355571195904,
    260290645593382686410768646144, 253444150194851058928840605696, 253440891761977878873643155456, 7966211570997820284793786466304, 253440891761977878873643155456, 484115205296444474196383236096,
    328791442340303941837221003264, 2059329575849794884788551680, 1544497181887346163591413760, 1630302580881087617124270080, 2102232275346665611554979840, 28144170869947196758776872960,
    49209396322910723601093099520, 1501594482390475436824985600, 28144170869947196758776872960, 1587399881384216890357841920, 1630302580881087617124270080, 1630302580881087617124270080,
    1587399881384216890357841920, 49209396322910723601093099520, 1587399881384216890357841920, 2059329575849794884788551680, 2102232275346665611554979840, 26357375115567333575766310912,
    4048572149218343576289580941312, 200627476378634731820521881600, 41081692327063036435520020283392, 125066478781486586069935718400, 6513879103202426357809152000, 199324700557994246548960051200,
    208444131302477643449892864000, 125066478781486586069935718400, 3193103536389829400598046310400, 204535803840556187635207372800, 4048577993761031015859302170624, 199324700557994246548960051200,
    6513879103202426357809152000, 204535803840556187635207372800, 6513879103202426357809152000, 199324700557994246548960051200
  ]
def negativeScales : Array ℕ := #[
    33, 33, 35, 34, 35, 48,
    37, 53, 37, 33, 36, 37,
    45, 37, 33, 50, 56, 35,
    32, 39, 40, 56, 39, 34,
    34, 35, 35, 40, 35, 50,
    32, 14, 16, 17, 18, 18,
    23, 18, 18, 18, 17, 17,
    18, 23, 18, 14, 18, 42,
    46, 34, 52, 29, 30, 35,
    30, 29, 39, 35, 47, 35,
    30, 35, 30, 35
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33398164099606948, 33589651375643197, 35586136320747890, 34577901066481477, 35586136320747890, 48100398511881668,
    37213170233416747, 53255999484567670, 37938206183912727, 33598834324356371, 36936083659826648, 37959085994884112,
    45105370587519431, 37213170233416747, 33598834324356371, 50611268248577278, 56624712015580999, 35677582616897647,
    32053087501319183, 39796799506051747, 40651736642736908, 56624711913084631, 39796799506051747, 34716020156082099,
    34716038216486737, 35677582616897647, 35677564068609325, 40651736642736908, 35677564068609325, 50611265159431559,
    32053087501319183, 14734233300001342, 16319195800563791, 17397198312565070, 18763980643541010, 18506822803739902,
    23312920475137304, 18278553816066445, 18506822803739902, 18358724164750430, 17397198312565070, 17397198312565070,
    18358724164750430, 23312920475137304, 18358724164750430, 14734233300001342, 18763980643541010, 42412193358894952,
    46675256034546678, 34340433951505530, 52018266555042936, 29658609911558268, 30395575505697996, 35331035253503280,
    30395575505697996, 29658609911558268, 39332802179677468, 35368268159702257, 47675258117228266, 35331035253503280,
    30395575505697996, 35368268159702257, 30395575505697996, 35331035253503280
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
noncomputable def negativeCeiling : ℝ := 92366126727 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 203924290487886149306023936, coefficient := (-203924290487886149306023936) }, { argument := 59614559484627989694538317824, coefficient := (-59614559484627989694538317824) }, { argument := 59469488368980411624470872064, coefficient := (-59469488368980411624470872064) }, { argument := 59130989099136062794313498624, coefficient := (-59130989099136062794313498624) }, { argument := 59469488368980411624470872064, coefficient := (-59469488368980411624470872064) }, { argument := 84938101057873082888350597120, coefficient := (-84938101057873082888350597120) }, { argument := 734751032742143515750247170048, coefficient := (-734751032742143515750247170048) }, { argument := 3027562280072335336988018212864, coefficient := (-3027562280072335336988018212864) }, { argument := 607250353057471333896208515072, coefficient := (-607250353057471333896208515072) }, { argument := 29997612205425489836253380608, coefficient := (-29997612205425489836253380608) }, { argument := 606357610230475254608640868352, coefficient := (-606357610230475254608640868352) }, { argument := 616102859244575770903444455424, coefficient := (-616102859244575770903444455424) }, { argument := 85231335056103622510209138688, coefficient := (-85231335056103622510209138688) }, { argument := 734751032742143515750247170048, coefficient := (-734751032742143515750247170048) }, { argument := 29997612205425489836253380608, coefficient := (-29997612205425489836253380608) }, { argument := 484116241900835640164478877696, coefficient := (-484116241900835640164478877696) }, { argument := 31273508352999470873547028561920, coefficient := (-31273508352999470873547028561920) }, { argument := 253444150194851058928840605696, coefficient := (-253444150194851058928840605696) }, { argument := 328791442340303941837221003264, coefficient := (-328791442340303941837221003264) }, { argument := 4404434073220642587089257365504, coefficient := (-4404434073220642587089257365504) }, { argument := 7966211570997820284793786466304, coefficient := (-7966211570997820284793786466304) }, { argument := 31273506131170988859459926753280, coefficient := (-31273506131170988859459926753280) }, { argument := 4404434073220642587089257365504, coefficient := (-4404434073220642587089257365504) }, { argument := 260287387160509506355571195904, coefficient := (-260287387160509506355571195904) }, { argument := 260290645593382686410768646144, coefficient := (-260290645593382686410768646144) }, { argument := 253444150194851058928840605696, coefficient := (-253444150194851058928840605696) }, { argument := 253440891761977878873643155456, coefficient := (-253440891761977878873643155456) }, { argument := 7966211570997820284793786466304, coefficient := (-7966211570997820284793786466304) }, { argument := 253440891761977878873643155456, coefficient := (-253440891761977878873643155456) }, { argument := 484115205296444474196383236096, coefficient := (-484115205296444474196383236096) }, { argument := 328791442340303941837221003264, coefficient := (-328791442340303941837221003264) }, { argument := 2059329575849794884788551680, coefficient := (-2059329575849794884788551680) }, { argument := 1544497181887346163591413760, coefficient := (-1544497181887346163591413760) }, { argument := 1630302580881087617124270080, coefficient := (-1630302580881087617124270080) }, { argument := 2102232275346665611554979840, coefficient := (-2102232275346665611554979840) }, { argument := 28144170869947196758776872960, coefficient := (-28144170869947196758776872960) }, { argument := 49209396322910723601093099520, coefficient := (-49209396322910723601093099520) }, { argument := 1501594482390475436824985600, coefficient := (-1501594482390475436824985600) }, { argument := 28144170869947196758776872960, coefficient := (-28144170869947196758776872960) }, { argument := 1587399881384216890357841920, coefficient := (-1587399881384216890357841920) }, { argument := 1630302580881087617124270080, coefficient := (-1630302580881087617124270080) }, { argument := 1630302580881087617124270080, coefficient := (-1630302580881087617124270080) }, { argument := 1587399881384216890357841920, coefficient := (-1587399881384216890357841920) }, { argument := 49209396322910723601093099520, coefficient := (-49209396322910723601093099520) }, { argument := 1587399881384216890357841920, coefficient := (-1587399881384216890357841920) }, { argument := 2059329575849794884788551680, coefficient := (-2059329575849794884788551680) }, { argument := 2102232275346665611554979840, coefficient := (-2102232275346665611554979840) }, { argument := 26357375115567333575766310912, coefficient := (-26357375115567333575766310912) }, { argument := 4048572149218343576289580941312, coefficient := (-4048572149218343576289580941312) }, { argument := 200627476378634731820521881600, coefficient := (-200627476378634731820521881600) }, { argument := 41081692327063036435520020283392, coefficient := (-41081692327063036435520020283392) }, { argument := 125066478781486586069935718400, coefficient := (-125066478781486586069935718400) }, { argument := 6513879103202426357809152000, coefficient := (-6513879103202426357809152000) }, { argument := 199324700557994246548960051200, coefficient := (-199324700557994246548960051200) }, { argument := 208444131302477643449892864000, coefficient := (-208444131302477643449892864000) }, { argument := 125066478781486586069935718400, coefficient := (-125066478781486586069935718400) }, { argument := 3193103536389829400598046310400, coefficient := (-3193103536389829400598046310400) }, { argument := 204535803840556187635207372800, coefficient := (-204535803840556187635207372800) }, { argument := 4048577993761031015859302170624, coefficient := (-4048577993761031015859302170624) }, { argument := 199324700557994246548960051200, coefficient := (-199324700557994246548960051200) }, { argument := 6513879103202426357809152000, coefficient := (-6513879103202426357809152000) }, { argument := 204535803840556187635207372800, coefficient := (-204535803840556187635207372800) }, { argument := 6513879103202426357809152000, coefficient := (-6513879103202426357809152000) }, { argument := 199324700557994246548960051200, coefficient := (-199324700557994246548960051200) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8
