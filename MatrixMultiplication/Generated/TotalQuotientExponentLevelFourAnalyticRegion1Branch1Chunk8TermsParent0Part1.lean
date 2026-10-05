import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
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

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-5231617703190538409203786349281280)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1412472375, 5852512944397, 2415, 7245, 15295, 39445,
    33005, 923335, 28175, 33005, 29785, 15295,
    15295, 29785, 923335, 29785, 2415, 39445,
    22737561, 10749734919, 408051366261, 42998969167, 22737561, 11062755551115,
    1155, 1714561876539851, 13035, 1155, 428640494935739, 1155,
    1155, 47883, 297, 13035, 47883, 44251168779549,
    1155, 297, 1155, 20799540327371, 42946054955, 745822374464717,
    17747414301, 1753384211, 17721363833, 36011378117, 2609027749357, 42946054955,
    1753384211, 53747703094043, 3472057580435685, 54956939649, 4455954951, 955059398151,
    1727396778351, 27776458670105145, 955059398151, 28220415063, 28220768343, 54956939649,
    54956233089, 1727396778351, 54956233089, 429980704062919
  ]
def negativeCoefficients : Array ℕ := #[
    208444131302477643449892864000, 26357375115567333575766310912, 182472240898083091057213440, 136854180673562318292910080, 144457190710982447086960640, 186273745916793155454238720,
    2493787292273802244448583680, 4360326256460443863387996160, 133052675654852253895884800, 2493787292273802244448583680, 140655685692272382689935360, 144457190710982447086960640,
    144457190710982447086960640, 140655685692272382689935360, 4360326256460443863387996160, 140655685692272382689935360, 182472240898083091057213440, 186273745916793155454238720,
    1677735874509437704605794304, 198297608911011876870348079104, 1881804780586046856848625106944, 198297744914244246312444755968, 1677735874509437704605794304, 12455555444423100028692725760,
    174538665206862087098204160, 482606264268033208202880352256, 1969793507334586411536875520, 174538665206862087098204160, 482606293317124784545266139136, 174538665206862087098204160,
    174538665206862087098204160, 7235874377575911096556978176, 179525484212772432443867136, 1969793507334586411536875520, 7235874377575911096556978176, 12455596701642862666023174144,
    174538665206862087098204160, 179525484212772432443867136, 174538665206862087098204160, 23418200516956409995936661504, 198053721182587743602286264320, 839721341930969503077559697408,
    163691004790319947235048030208, 8086057450800037000845983744, 163450731632221767077214552064, 166073168966470895519576096768, 23500032799606938069729542144, 198053721182587743602286264320,
    8086057450800037000845983744, 484116271252704219454983110656, 31273514450918113817621189099520, 253444150194851058928840605696, 328791442340303941837221003264, 4404434073220642587089257365504,
    7966211570997820284793786466304, 31273512229089378476055047700480, 4404434073220642587089257365504, 260287387160509506355571195904, 260290645593382686410768646144, 253444150194851058928840605696,
    253440891761977878873643155456, 7966211570997820284793786466304, 253440891761977878873643155456, 484115234648566380965927059456
  ]
def negativeScales : Array ℕ := #[
    30, 42, 11, 12, 13, 15,
    15, 19, 14, 15, 14, 13,
    13, 14, 19, 14, 11, 15,
    24, 33, 38, 35, 24, 43,
    10, 50, 13, 10, 48, 10,
    10, 15, 8, 13, 15, 45,
    10, 8, 10, 44, 35, 49,
    34, 30, 34, 35, 41, 35,
    30, 45, 51, 35, 32, 39,
    40, 54, 39, 34, 34, 35,
    35, 40, 35, 48
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30395575505697996, 42412193358894952, 11237807473723136, 12822769975464802, 13900772490874059, 15267554817117188,
    15010396977620064, 19816494649918742, 14782127990393705, 15010396977620064, 14862298340817341, 13900772490874059,
    13900772490874059, 14862298340817341, 19816494649918742, 14862298340817341, 11237807473723136, 15267554817117188,
    24438574172534924, 33323582033268887, 38569959816512928, 35323583022746887, 24438574172534924, 43330776015562349,
    10173677136303420, 50606761393712908, 13670102962458164, 10173677136303420, 48606761480551770, 10173677136303420,
    10173677136303420, 15547225923426421, 8214319120800766, 13670102962458164, 15547225923426421, 45330780794272383,
    10173677136303420, 8214319120800766, 10173677136303420, 44241616878500623, 35321806559672488, 49405825406635596,
    34046889796203128, 30707495015925472, 34044770586592225, 35067733759857468, 41246649427244815, 35321806559672488,
    30707495015925472, 45611268336047580, 51624712296887338, 35677582616897647, 32053087501319183, 39796799506051747,
    40651736642736908, 54624712194390977, 39796799506051747, 34716020156082099, 34716038216486737, 35677582616897647,
    35677564068609325, 40651736642736908, 35677564068609325, 48611265246902804
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
noncomputable def negativeCeiling : ℝ := 55968192407 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 208444131302477643449892864000, coefficient := (-208444131302477643449892864000) }, { argument := 26357375115567333575766310912, coefficient := (-26357375115567333575766310912) }, { argument := 182472240898083091057213440, coefficient := (-182472240898083091057213440) }, { argument := 136854180673562318292910080, coefficient := (-136854180673562318292910080) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 186273745916793155454238720, coefficient := (-186273745916793155454238720) }, { argument := 2493787292273802244448583680, coefficient := (-2493787292273802244448583680) }, { argument := 4360326256460443863387996160, coefficient := (-4360326256460443863387996160) }, { argument := 133052675654852253895884800, coefficient := (-133052675654852253895884800) }, { argument := 2493787292273802244448583680, coefficient := (-2493787292273802244448583680) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 4360326256460443863387996160, coefficient := (-4360326256460443863387996160) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 182472240898083091057213440, coefficient := (-182472240898083091057213440) }, { argument := 186273745916793155454238720, coefficient := (-186273745916793155454238720) }, { argument := 1677735874509437704605794304, coefficient := (-1677735874509437704605794304) }, { argument := 198297608911011876870348079104, coefficient := (-198297608911011876870348079104) }, { argument := 1881804780586046856848625106944, coefficient := (-1881804780586046856848625106944) }, { argument := 198297744914244246312444755968, coefficient := (-198297744914244246312444755968) }, { argument := 1677735874509437704605794304, coefficient := (-1677735874509437704605794304) }, { argument := 12455555444423100028692725760, coefficient := (-12455555444423100028692725760) }, { argument := 174538665206862087098204160, coefficient := (-174538665206862087098204160) }, { argument := 482606264268033208202880352256, coefficient := (-482606264268033208202880352256) }, { argument := 1969793507334586411536875520, coefficient := (-1969793507334586411536875520) }, { argument := 174538665206862087098204160, coefficient := (-174538665206862087098204160) }, { argument := 482606293317124784545266139136, coefficient := (-482606293317124784545266139136) }, { argument := 174538665206862087098204160, coefficient := (-174538665206862087098204160) }, { argument := 174538665206862087098204160, coefficient := (-174538665206862087098204160) }, { argument := 7235874377575911096556978176, coefficient := (-7235874377575911096556978176) }, { argument := 179525484212772432443867136, coefficient := (-179525484212772432443867136) }, { argument := 1969793507334586411536875520, coefficient := (-1969793507334586411536875520) }, { argument := 7235874377575911096556978176, coefficient := (-7235874377575911096556978176) }, { argument := 12455596701642862666023174144, coefficient := (-12455596701642862666023174144) }, { argument := 174538665206862087098204160, coefficient := (-174538665206862087098204160) }, { argument := 179525484212772432443867136, coefficient := (-179525484212772432443867136) }, { argument := 174538665206862087098204160, coefficient := (-174538665206862087098204160) }, { argument := 23418200516956409995936661504, coefficient := (-23418200516956409995936661504) }, { argument := 198053721182587743602286264320, coefficient := (-198053721182587743602286264320) }, { argument := 839721341930969503077559697408, coefficient := (-839721341930969503077559697408) }, { argument := 163691004790319947235048030208, coefficient := (-163691004790319947235048030208) }, { argument := 8086057450800037000845983744, coefficient := (-8086057450800037000845983744) }, { argument := 163450731632221767077214552064, coefficient := (-163450731632221767077214552064) }, { argument := 166073168966470895519576096768, coefficient := (-166073168966470895519576096768) }, { argument := 23500032799606938069729542144, coefficient := (-23500032799606938069729542144) }, { argument := 198053721182587743602286264320, coefficient := (-198053721182587743602286264320) }, { argument := 8086057450800037000845983744, coefficient := (-8086057450800037000845983744) }, { argument := 484116271252704219454983110656, coefficient := (-484116271252704219454983110656) }, { argument := 31273514450918113817621189099520, coefficient := (-31273514450918113817621189099520) }, { argument := 253444150194851058928840605696, coefficient := (-253444150194851058928840605696) }, { argument := 328791442340303941837221003264, coefficient := (-328791442340303941837221003264) }, { argument := 4404434073220642587089257365504, coefficient := (-4404434073220642587089257365504) }, { argument := 7966211570997820284793786466304, coefficient := (-7966211570997820284793786466304) }, { argument := 31273512229089378476055047700480, coefficient := (-31273512229089378476055047700480) }, { argument := 4404434073220642587089257365504, coefficient := (-4404434073220642587089257365504) }, { argument := 260287387160509506355571195904, coefficient := (-260287387160509506355571195904) }, { argument := 260290645593382686410768646144, coefficient := (-260290645593382686410768646144) }, { argument := 253444150194851058928840605696, coefficient := (-253444150194851058928840605696) }, { argument := 253440891761977878873643155456, coefficient := (-253440891761977878873643155456) }, { argument := 7966211570997820284793786466304, coefficient := (-7966211570997820284793786466304) }, { argument := 253440891761977878873643155456, coefficient := (-253440891761977878873643155456) }, { argument := 484115234648566380965927059456, coefficient := (-484115234648566380965927059456) }] }

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


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-33400300191506129851408364945276928)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4455954951, 57580806305905, 4562208630456765, 825691406925, 23245169043207385, 32169795075,
    53616325125, 1640659548825, 53616325125, 32169795075, 26282722576275, 1683552608925,
    142569225735645, 1640659548825, 53616325125, 1683552608925, 53616325125, 1640659548825,
    53616325125, 57580806305905, 2415, 7245, 15295, 39445,
    33005, 923335, 28175, 33005, 29785, 15295,
    15295, 29785, 923335, 29785, 2415, 39445,
    885879, 418820841, 15898105179, 1675284513, 885879, 706486146938997,
    3465, 111237601668810293, 39105, 3465, 27809405783179589, 3465,
    3465, 143649, 891, 39105, 143649, 2825973658702563,
    3465, 891, 3465, 1476465, 698034735, 26496841965,
    2792140855, 1476465, 1422411269, 7315
  ]
def negativeCoefficients : Array ℕ := #[
    328791442340303941837221003264, 259320897822966464310547578880, 41092722176223095484752729210880, 1903914758425830697203243417600, 418747738564611872477910233251840, 1186855953304413941113710182400,
    61815414234604892766339072000, 1891551675578909718649975603200, 1978093255507356568522850304000, 1186855953304413941113710182400, 30301916057803318434059413094400, 1941004006966593632863046860800,
    41092781561443260829604385914880, 1891551675578909718649975603200, 61815414234604892766339072000, 1941004006966593632863046860800, 61815414234604892766339072000, 1891551675578909718649975603200,
    1978093255507356568522850304000, 259320897822966464310547578880, 182472240898083091057213440, 136854180673562318292910080, 144457190710982447086960640, 186273745916793155454238720,
    2493787292273802244448583680, 4360326256460443863387996160, 133052675654852253895884800, 2493787292273802244448583680, 140655685692272382689935360, 144457190710982447086960640,
    144457190710982447086960640, 140655685692272382689935360, 4360326256460443863387996160, 140655685692272382689935360, 182472240898083091057213440, 186273745916793155454238720,
    1045861324369519608065949696, 123614093866604806360736464896, 1173073109975717521152389677056, 123614178647840569129835692032, 1045861324369519608065949696, 795432687024221093112607408128,
    130903998905146565323653120, 31310601339077606222278015582208, 1477345130500939808652656640, 130903998905146565323653120, 31310607380630628374864552001536, 130903998905146565323653120,
    130903998905146565323653120, 5426905783181933322417733632, 134644113159579324332900352, 1477345130500939808652656640, 5426905783181933322417733632, 795440869768231247962416611328,
    130903998905146565323653120, 134644113159579324332900352, 130903998905146565323653120, 54471943977579146253434880, 6438234055552333664621690880, 61097557811235287560020295680,
    6438238471241696308845608960, 54471943977579146253434880, 6559714161700858212883890176, 138176443288765818952744960
  ]
def negativeScales : Array ℕ := #[
    32, 45, 52, 39, 54, 34,
    35, 40, 35, 34, 44, 40,
    47, 40, 35, 40, 35, 40,
    35, 45, 11, 12, 13, 15,
    15, 19, 14, 15, 14, 13,
    13, 14, 19, 14, 11, 15,
    19, 28, 33, 30, 19, 49,
    11, 56, 15, 11, 54, 11,
    11, 17, 9, 15, 17, 51,
    11, 9, 11, 20, 29, 34,
    31, 20, 30, 12
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32053087501319183, 45710653224776941, 52018653846120742, 39586811734751072, 54367780435640404, 34904987699548277,
    35641953288956962, 40577413036747902, 35641953288956962, 34904987699548277, 44579179962922245, 40614645942952326,
    47018655931032527, 40577413036747902, 35641953288956962, 40614645942952326, 35641953288956962, 40577413036747902,
    35641953288956962, 45710653224776941, 11237807473723136, 12822769975464802, 13900772490874059, 15267554817117188,
    15010396977620064, 19816494649918742, 14782127990393705, 15010396977620064, 14862298340817341, 13900772490874059,
    13900772490874059, 14862298340817341, 19816494649918742, 14862298340817341, 11237807473723136, 15267554817117188,
    19756750132821590, 28641757993312392, 33888135780062040, 30641758982790393, 19756750132821590, 49327654600322199,
    11758639637295877, 56626422158095198, 15255065463144076, 11758639637295877, 54626422436471128, 11758639637295877,
    11758639637295877, 17132188424146355, 9799281622158559, 15255065463144076, 17132188424146355, 51327669441481830,
    11758639637295877, 9799281622158559, 11758639637295877, 20493715726727574, 29378723587461350, 34625101370714141,
    31378724576939351, 20493715726727574, 30405691513009289, 12836642150365173
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
noncomputable def negativeCeiling : ℝ := 391550692417 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 328791442340303941837221003264, coefficient := (-328791442340303941837221003264) }, { argument := 259320897822966464310547578880, coefficient := (-259320897822966464310547578880) }, { argument := 41092722176223095484752729210880, coefficient := (-41092722176223095484752729210880) }, { argument := 1903914758425830697203243417600, coefficient := (-1903914758425830697203243417600) }, { argument := 418747738564611872477910233251840, coefficient := (-418747738564611872477910233251840) }, { argument := 1186855953304413941113710182400, coefficient := (-1186855953304413941113710182400) }, { argument := 61815414234604892766339072000, coefficient := (-61815414234604892766339072000) }, { argument := 1891551675578909718649975603200, coefficient := (-1891551675578909718649975603200) }, { argument := 1978093255507356568522850304000, coefficient := (-1978093255507356568522850304000) }, { argument := 1186855953304413941113710182400, coefficient := (-1186855953304413941113710182400) }, { argument := 30301916057803318434059413094400, coefficient := (-30301916057803318434059413094400) }, { argument := 1941004006966593632863046860800, coefficient := (-1941004006966593632863046860800) }, { argument := 41092781561443260829604385914880, coefficient := (-41092781561443260829604385914880) }, { argument := 1891551675578909718649975603200, coefficient := (-1891551675578909718649975603200) }, { argument := 61815414234604892766339072000, coefficient := (-61815414234604892766339072000) }, { argument := 1941004006966593632863046860800, coefficient := (-1941004006966593632863046860800) }, { argument := 61815414234604892766339072000, coefficient := (-61815414234604892766339072000) }, { argument := 1891551675578909718649975603200, coefficient := (-1891551675578909718649975603200) }, { argument := 1978093255507356568522850304000, coefficient := (-1978093255507356568522850304000) }, { argument := 259320897822966464310547578880, coefficient := (-259320897822966464310547578880) }, { argument := 182472240898083091057213440, coefficient := (-182472240898083091057213440) }, { argument := 136854180673562318292910080, coefficient := (-136854180673562318292910080) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 186273745916793155454238720, coefficient := (-186273745916793155454238720) }, { argument := 2493787292273802244448583680, coefficient := (-2493787292273802244448583680) }, { argument := 4360326256460443863387996160, coefficient := (-4360326256460443863387996160) }, { argument := 133052675654852253895884800, coefficient := (-133052675654852253895884800) }, { argument := 2493787292273802244448583680, coefficient := (-2493787292273802244448583680) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 4360326256460443863387996160, coefficient := (-4360326256460443863387996160) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 182472240898083091057213440, coefficient := (-182472240898083091057213440) }, { argument := 186273745916793155454238720, coefficient := (-186273745916793155454238720) }, { argument := 1045861324369519608065949696, coefficient := (-1045861324369519608065949696) }, { argument := 123614093866604806360736464896, coefficient := (-123614093866604806360736464896) }, { argument := 1173073109975717521152389677056, coefficient := (-1173073109975717521152389677056) }, { argument := 123614178647840569129835692032, coefficient := (-123614178647840569129835692032) }, { argument := 1045861324369519608065949696, coefficient := (-1045861324369519608065949696) }, { argument := 795432687024221093112607408128, coefficient := (-795432687024221093112607408128) }, { argument := 130903998905146565323653120, coefficient := (-130903998905146565323653120) }, { argument := 31310601339077606222278015582208, coefficient := (-31310601339077606222278015582208) }, { argument := 1477345130500939808652656640, coefficient := (-1477345130500939808652656640) }, { argument := 130903998905146565323653120, coefficient := (-130903998905146565323653120) }, { argument := 31310607380630628374864552001536, coefficient := (-31310607380630628374864552001536) }, { argument := 130903998905146565323653120, coefficient := (-130903998905146565323653120) }, { argument := 130903998905146565323653120, coefficient := (-130903998905146565323653120) }, { argument := 5426905783181933322417733632, coefficient := (-5426905783181933322417733632) }, { argument := 134644113159579324332900352, coefficient := (-134644113159579324332900352) }, { argument := 1477345130500939808652656640, coefficient := (-1477345130500939808652656640) }, { argument := 5426905783181933322417733632, coefficient := (-5426905783181933322417733632) }, { argument := 795440869768231247962416611328, coefficient := (-795440869768231247962416611328) }, { argument := 130903998905146565323653120, coefficient := (-130903998905146565323653120) }, { argument := 134644113159579324332900352, coefficient := (-134644113159579324332900352) }, { argument := 130903998905146565323653120, coefficient := (-130903998905146565323653120) }, { argument := 54471943977579146253434880, coefficient := (-54471943977579146253434880) }, { argument := 6438234055552333664621690880, coefficient := (-6438234055552333664621690880) }, { argument := 61097557811235287560020295680, coefficient := (-61097557811235287560020295680) }, { argument := 6438238471241696308845608960, coefficient := (-6438238471241696308845608960) }, { argument := 54471943977579146253434880, coefficient := (-54471943977579146253434880) }, { argument := 6559714161700858212883890176, coefficient := (-6559714161700858212883890176) }, { argument := 138176443288765818952744960, coefficient := (-138176443288765818952744960) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk8
