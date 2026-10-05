import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 16, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-55262141797447888828422732906496)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    695817271, 7811913641, 12103462845, 3390075731, 652747501, 13539246553,
    6801207833, 695817271, 7811913641, 652747501, 383320953, 1856437383,
    383320953, 38314989, 267987523, 3939555, 37031817, 437290605,
    30728529, 267987465, 437290605, 3939555, 30728529, 30728529,
    30728529, 30728529, 30728529, 38315047, 37031817, 21534885,
    104294235, 21534885, 27160443, 2283901061, 1141950255, 13580497,
    1566565, 554396885, 56823585, 20049585395, 1873305, 4371045,
    56823585, 56823585, 1873305, 701240505, 28099575, 554396885,
    56823585, 4371045, 28099575, 4371045, 56823585, 56823585,
    27561345, 377137389, 27946605267, 48412217785, 12127772097, 2335161087,
    48435760611, 24330871971, 377137389, 27946605267
  ]
def negativeCoefficients : Array ℕ := #[
    802222695012750190754922496, 18013046457680944467627999232, 13954342594210468706616606720, 15633964850062706519073357824, 752566630981279351073406976, 15609688507127826540006473728,
    15682517535932466477207126016, 802222695012750190754922496, 18013046457680944467627999232, 752566630981279351073406976, 883877939760180946330976256, 8561306323267029776027615232,
    883877939760180946330976256, 2827147185079986637447888896, 19773989006913408636049948672, 2325502811177690643730268160, 2732465803133786506383065088, 32266351505090457681757470720,
    72555687708743948084384366592, 19773984727268783535433973760, 32266351505090457681757470720, 2325502811177690643730268160, 2267365240898248377637011456, 2267365240898248377637011456,
    2267365240898248377637011456, 72555687708743948084384366592, 2267365240898248377637011456, 2827151464724611738063863808, 2732465803133786506383065088, 49656064031470839681515520,
    480972265352080324495933440, 49656064031470839681515520, 250510870474788037610962944, 21065269180970353570808332288, 21065264098892361263826862080, 250515952552780344592433152,
    57796047259661607454638080, 5113408726428392905328558080, 1048210129845680971563663360, 46231196320693728694019031040, 552902046512007545440174080, 40315774224833883521679360,
    1048210129845680971563663360, 1048210129845680971563663360, 552902046512007545440174080, 12935604129853843198527406080, 1036691337210014147700326400, 5113408726428392905328558080,
    1048210129845680971563663360, 40315774224833883521679360, 1036691337210014147700326400, 40315774224833883521679360, 1048210129845680971563663360, 1048210129845680971563663360,
    63552134692776797735485440, 3478478447755021920409485312, 64440484386166548927489245184, 55815486970036556604280668160, 55929477014408702842726514688, 2692257433923400292118822912,
    55842630000411173801045262336, 56103171042403760926089019392, 3478478447755021920409485312, 64440484386166548927489245184
  ]
def negativeScales : Array ℕ := #[
    29, 32, 33, 31, 29, 33,
    32, 29, 32, 29, 28, 30,
    28, 25, 27, 21, 25, 28,
    24, 27, 28, 21, 24, 24,
    24, 24, 24, 25, 25, 24,
    26, 24, 24, 31, 30, 23,
    20, 29, 25, 34, 20, 22,
    25, 25, 20, 29, 24, 29,
    25, 22, 24, 22, 25, 25,
    24, 28, 34, 35, 33, 31,
    35, 34, 28, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    29374133247882541, 32863028856836993, 33494700815760347, 31658670356140714, 29281949788386448, 33656428405352591,
    32663143832723161, 29374133247882541, 32863028856836993, 29281949788386448, 28513977619651006, 30789889508912656,
    28513977619651006, 25191405555724780, 27997590614934061, 21909601251003093, 25142262002610578, 28704017112249948,
    24873075372468708, 27997590302694331, 28704017112249948, 21909601251003093, 24873075372468708, 24873075372468708,
    24873075372468708, 24873075372468708, 24873075372468708, 25191407739628553, 25142262002610578, 24360172283571542,
    26636084172323563, 24360172283571542, 24695003675106339, 31088853008235029, 30088852660179206, 23695032942556270,
    20579173200659118, 29046343910499571, 25759986518520320, 34222853352398611, 20837154380116192, 22059546800099931,
    25759986518520320, 25759986518520320, 20837154380116192, 29385334090442932, 24744044974569330, 29046343910499571,
    25759986518520320, 22059546800099931, 24744044974569330, 22059546800099931, 25759986518520320, 25759986518520320,
    24716142957928118, 28490514943922275, 34701953995455768, 35494652135081148, 33497595496874045, 31120874929146053,
    35495353546087357, 34502068973453393, 28490514943922275, 34701953995455768
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
noncomputable def negativeCeiling : ℝ := 326318403 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 802222695012750190754922496, coefficient := (-802222695012750190754922496) }, { argument := 18013046457680944467627999232, coefficient := (-18013046457680944467627999232) }, { argument := 13954342594210468706616606720, coefficient := (-13954342594210468706616606720) }, { argument := 15633964850062706519073357824, coefficient := (-15633964850062706519073357824) }, { argument := 752566630981279351073406976, coefficient := (-752566630981279351073406976) }, { argument := 15609688507127826540006473728, coefficient := (-15609688507127826540006473728) }, { argument := 15682517535932466477207126016, coefficient := (-15682517535932466477207126016) }, { argument := 802222695012750190754922496, coefficient := (-802222695012750190754922496) }, { argument := 18013046457680944467627999232, coefficient := (-18013046457680944467627999232) }, { argument := 752566630981279351073406976, coefficient := (-752566630981279351073406976) }, { argument := 883877939760180946330976256, coefficient := (-883877939760180946330976256) }, { argument := 8561306323267029776027615232, coefficient := (-8561306323267029776027615232) }, { argument := 883877939760180946330976256, coefficient := (-883877939760180946330976256) }, { argument := 2827147185079986637447888896, coefficient := (-2827147185079986637447888896) }, { argument := 19773989006913408636049948672, coefficient := (-19773989006913408636049948672) }, { argument := 2325502811177690643730268160, coefficient := (-2325502811177690643730268160) }, { argument := 2732465803133786506383065088, coefficient := (-2732465803133786506383065088) }, { argument := 32266351505090457681757470720, coefficient := (-32266351505090457681757470720) }, { argument := 72555687708743948084384366592, coefficient := (-72555687708743948084384366592) }, { argument := 19773984727268783535433973760, coefficient := (-19773984727268783535433973760) }, { argument := 32266351505090457681757470720, coefficient := (-32266351505090457681757470720) }, { argument := 2325502811177690643730268160, coefficient := (-2325502811177690643730268160) }, { argument := 2267365240898248377637011456, coefficient := (-2267365240898248377637011456) }, { argument := 2267365240898248377637011456, coefficient := (-2267365240898248377637011456) }, { argument := 2267365240898248377637011456, coefficient := (-2267365240898248377637011456) }, { argument := 72555687708743948084384366592, coefficient := (-72555687708743948084384366592) }, { argument := 2267365240898248377637011456, coefficient := (-2267365240898248377637011456) }, { argument := 2827151464724611738063863808, coefficient := (-2827151464724611738063863808) }, { argument := 2732465803133786506383065088, coefficient := (-2732465803133786506383065088) }, { argument := 49656064031470839681515520, coefficient := (-49656064031470839681515520) }, { argument := 480972265352080324495933440, coefficient := (-480972265352080324495933440) }, { argument := 49656064031470839681515520, coefficient := (-49656064031470839681515520) }, { argument := 250510870474788037610962944, coefficient := (-250510870474788037610962944) }, { argument := 21065269180970353570808332288, coefficient := (-21065269180970353570808332288) }, { argument := 21065264098892361263826862080, coefficient := (-21065264098892361263826862080) }, { argument := 250515952552780344592433152, coefficient := (-250515952552780344592433152) }, { argument := 57796047259661607454638080, coefficient := (-57796047259661607454638080) }, { argument := 5113408726428392905328558080, coefficient := (-5113408726428392905328558080) }, { argument := 1048210129845680971563663360, coefficient := (-1048210129845680971563663360) }, { argument := 46231196320693728694019031040, coefficient := (-46231196320693728694019031040) }, { argument := 552902046512007545440174080, coefficient := (-552902046512007545440174080) }, { argument := 40315774224833883521679360, coefficient := (-40315774224833883521679360) }, { argument := 1048210129845680971563663360, coefficient := (-1048210129845680971563663360) }, { argument := 1048210129845680971563663360, coefficient := (-1048210129845680971563663360) }, { argument := 552902046512007545440174080, coefficient := (-552902046512007545440174080) }, { argument := 12935604129853843198527406080, coefficient := (-12935604129853843198527406080) }, { argument := 1036691337210014147700326400, coefficient := (-1036691337210014147700326400) }, { argument := 5113408726428392905328558080, coefficient := (-5113408726428392905328558080) }, { argument := 1048210129845680971563663360, coefficient := (-1048210129845680971563663360) }, { argument := 40315774224833883521679360, coefficient := (-40315774224833883521679360) }, { argument := 1036691337210014147700326400, coefficient := (-1036691337210014147700326400) }, { argument := 40315774224833883521679360, coefficient := (-40315774224833883521679360) }, { argument := 1048210129845680971563663360, coefficient := (-1048210129845680971563663360) }, { argument := 1048210129845680971563663360, coefficient := (-1048210129845680971563663360) }, { argument := 63552134692776797735485440, coefficient := (-63552134692776797735485440) }, { argument := 3478478447755021920409485312, coefficient := (-3478478447755021920409485312) }, { argument := 64440484386166548927489245184, coefficient := (-64440484386166548927489245184) }, { argument := 55815486970036556604280668160, coefficient := (-55815486970036556604280668160) }, { argument := 55929477014408702842726514688, coefficient := (-55929477014408702842726514688) }, { argument := 2692257433923400292118822912, coefficient := (-2692257433923400292118822912) }, { argument := 55842630000411173801045262336, coefficient := (-55842630000411173801045262336) }, { argument := 56103171042403760926089019392, coefficient := (-56103171042403760926089019392) }, { argument := 3478478447755021920409485312, coefficient := (-3478478447755021920409485312) }, { argument := 64440484386166548927489245184, coefficient := (-64440484386166548927489245184) }] }

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


end Parent3

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1075027470212549893814446387625984)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    2335161087, 20990939013, 19779997051, 145482525, 1367535735, 16148560275,
    1134763695, 9889998105, 16148560275, 145482525, 1134763695, 1134763695,
    1134763695, 1134763695, 1134763695, 10495469927, 1367535735, 1164319449,
    5638841639, 1164319449, 427419603, 35941390381, 17970690855, 213714137,
    551267103, 1050410361, 9071725845, 84743451381, 299067885, 697825065,
    9071725845, 9071725845, 299067885, 111951078285, 4486018275, 1050410361,
    9071725845, 697825065, 4486018275, 697825065, 9071725845, 9071725845,
    650950371, 12865473, 1081847871, 540923805, 6432867, 57222347,
    9135387079, 364629700981, 9135387079, 228863271, 19754883, 53384319,
    43450587729, 840100599, 25287309, 43450577109, 25287309, 25287309,
    2166279471, 25287309, 840100599, 2166279471
  ]
def negativeCoefficients : Array ℕ := #[
    2692257433923400292118822912, 96803619959914093661757898752, 91219135844631664398753071104, 85877724987905653942832332800, 100906326860789143382827991040, 1191553434207190948456798617600,
    2679385019622656403016368783360, 91219131966203722901319843840, 1191553434207190948456798617600, 85877724987905653942832332800, 83730781863208012594261524480, 83730781863208012594261524480,
    83730781863208012594261524480, 2679385019622656403016368783360, 83730781863208012594261524480, 96803623838342035159191126016, 100906326860789143382827991040, 1342368930984095032723636224,
    13002283573351238105540067328, 1342368930984095032723636224, 1971125007156884822254682112, 165750407502898308359781351424, 165750367514968842575900835840, 1971164995086350606135197696,
    5084541582648141491390644224, 155013208813918885776885547008, 167343804969571524418228715520, 781620379774077633842902990848, 88269259764169595297527234560, 6436300191137366323778027520,
    167343804969571524418228715520, 167343804969571524418228715520, 88269259764169595297527234560, 2065132889899217823315064258560, 165504862057817991182863564800, 155013208813918885776885547008,
    167343804969571524418228715520, 6436300191137366323778027520, 165504862057817991182863564800, 6436300191137366323778027520, 167343804969571524418228715520, 167343804969571524418228715520,
    6003957449261641985339424768, 237326087818220246157754368, 19956570803024545488134209536, 19956565988424342249941237760, 237330902418423484350726144, 1055565990406001539785162752,
    168518147460586061431689969664, 1681557693917436907296416333824, 168518147460586061431689969664, 1055445547002258271695273984, 2915306167256604545252327424, 246191717535567554203877376,
    100190233961140964369532715008, 1937140093240386808077877248, 233234258717906103982620672, 100190209473088206520102944768, 233234258717906103982620672, 233234258717906103982620672,
    9990200748416978120588918784, 233234258717906103982620672, 1937140093240386808077877248, 9990200748416978120588918784
  ]
def negativeScales : Array ℕ := #[
    31, 34, 34, 27, 30, 33,
    30, 33, 33, 27, 30, 30,
    30, 30, 30, 33, 30, 30,
    32, 30, 28, 35, 34, 27,
    29, 29, 33, 36, 28, 29,
    33, 33, 28, 36, 32, 29,
    33, 29, 32, 29, 33, 33,
    29, 23, 30, 29, 22, 25,
    33, 38, 33, 27, 24, 25,
    35, 29, 24, 35, 24, 24,
    31, 24, 29, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    31120874929146053, 34289047654765104, 34203323159879243, 27116270629690011, 30348931386480287, 33910686501323470,
    30079744753664897, 33203323098539165, 33910686501323470, 27116270629690011, 30079744753664897, 30079744753664897,
    30079744753664897, 30079744753664897, 30079744753664897, 33289047712566544, 30348931386480287, 30116839792180295,
    32392751680917429, 30116839792180295, 28671077835832628, 35064927168989549, 34064926820933726, 27671107103282540,
    29038176269915125, 29968305919956791, 33078729895497072, 36302382835999486, 28155897756019532, 29378290177355982,
    33078729895497072, 33078729895497072, 28155897756019532, 36704077467778628, 32062788351628050, 29968305919956791,
    33078729895497072, 29378290177355982, 32062788351628050, 29378290177355982, 33078729895497072, 33078729895497072,
    29277972314407601, 23617001163049725, 30010850496233756, 29010850148177933, 22617030430499618, 25770075336211188,
    33088818713120656, 38407641124920806, 33088818713120656, 27769910710770090, 24235705966066496, 25669912694114257,
    35338656640481288, 29645986854852928, 24591910182082417, 35338656287864119, 24591910182082417, 24591910182082417,
    31012572230550626, 24591910182082417, 29645986854852928, 31012572230550626
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
noncomputable def negativeCeiling : ℝ := 64489193 / 10000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 2692257433923400292118822912, coefficient := (-2692257433923400292118822912) }, { argument := 96803619959914093661757898752, coefficient := (-96803619959914093661757898752) }, { argument := 91219135844631664398753071104, coefficient := (-91219135844631664398753071104) }, { argument := 85877724987905653942832332800, coefficient := (-85877724987905653942832332800) }, { argument := 100906326860789143382827991040, coefficient := (-100906326860789143382827991040) }, { argument := 1191553434207190948456798617600, coefficient := (-1191553434207190948456798617600) }, { argument := 2679385019622656403016368783360, coefficient := (-2679385019622656403016368783360) }, { argument := 91219131966203722901319843840, coefficient := (-91219131966203722901319843840) }, { argument := 1191553434207190948456798617600, coefficient := (-1191553434207190948456798617600) }, { argument := 85877724987905653942832332800, coefficient := (-85877724987905653942832332800) }, { argument := 83730781863208012594261524480, coefficient := (-83730781863208012594261524480) }, { argument := 83730781863208012594261524480, coefficient := (-83730781863208012594261524480) }, { argument := 83730781863208012594261524480, coefficient := (-83730781863208012594261524480) }, { argument := 2679385019622656403016368783360, coefficient := (-2679385019622656403016368783360) }, { argument := 83730781863208012594261524480, coefficient := (-83730781863208012594261524480) }, { argument := 96803623838342035159191126016, coefficient := (-96803623838342035159191126016) }, { argument := 100906326860789143382827991040, coefficient := (-100906326860789143382827991040) }, { argument := 1342368930984095032723636224, coefficient := (-1342368930984095032723636224) }, { argument := 13002283573351238105540067328, coefficient := (-13002283573351238105540067328) }, { argument := 1342368930984095032723636224, coefficient := (-1342368930984095032723636224) }, { argument := 1971125007156884822254682112, coefficient := (-1971125007156884822254682112) }, { argument := 165750407502898308359781351424, coefficient := (-165750407502898308359781351424) }, { argument := 165750367514968842575900835840, coefficient := (-165750367514968842575900835840) }, { argument := 1971164995086350606135197696, coefficient := (-1971164995086350606135197696) }, { argument := 5084541582648141491390644224, coefficient := (-5084541582648141491390644224) }, { argument := 155013208813918885776885547008, coefficient := (-155013208813918885776885547008) }, { argument := 167343804969571524418228715520, coefficient := (-167343804969571524418228715520) }, { argument := 781620379774077633842902990848, coefficient := (-781620379774077633842902990848) }, { argument := 88269259764169595297527234560, coefficient := (-88269259764169595297527234560) }, { argument := 6436300191137366323778027520, coefficient := (-6436300191137366323778027520) }, { argument := 167343804969571524418228715520, coefficient := (-167343804969571524418228715520) }, { argument := 167343804969571524418228715520, coefficient := (-167343804969571524418228715520) }, { argument := 88269259764169595297527234560, coefficient := (-88269259764169595297527234560) }, { argument := 2065132889899217823315064258560, coefficient := (-2065132889899217823315064258560) }, { argument := 165504862057817991182863564800, coefficient := (-165504862057817991182863564800) }, { argument := 155013208813918885776885547008, coefficient := (-155013208813918885776885547008) }, { argument := 167343804969571524418228715520, coefficient := (-167343804969571524418228715520) }, { argument := 6436300191137366323778027520, coefficient := (-6436300191137366323778027520) }, { argument := 165504862057817991182863564800, coefficient := (-165504862057817991182863564800) }, { argument := 6436300191137366323778027520, coefficient := (-6436300191137366323778027520) }, { argument := 167343804969571524418228715520, coefficient := (-167343804969571524418228715520) }, { argument := 167343804969571524418228715520, coefficient := (-167343804969571524418228715520) }, { argument := 6003957449261641985339424768, coefficient := (-6003957449261641985339424768) }, { argument := 237326087818220246157754368, coefficient := (-237326087818220246157754368) }, { argument := 19956570803024545488134209536, coefficient := (-19956570803024545488134209536) }, { argument := 19956565988424342249941237760, coefficient := (-19956565988424342249941237760) }, { argument := 237330902418423484350726144, coefficient := (-237330902418423484350726144) }, { argument := 1055565990406001539785162752, coefficient := (-1055565990406001539785162752) }, { argument := 168518147460586061431689969664, coefficient := (-168518147460586061431689969664) }, { argument := 1681557693917436907296416333824, coefficient := (-1681557693917436907296416333824) }, { argument := 168518147460586061431689969664, coefficient := (-168518147460586061431689969664) }, { argument := 1055445547002258271695273984, coefficient := (-1055445547002258271695273984) }, { argument := 2915306167256604545252327424, coefficient := (-2915306167256604545252327424) }, { argument := 246191717535567554203877376, coefficient := (-246191717535567554203877376) }, { argument := 100190233961140964369532715008, coefficient := (-100190233961140964369532715008) }, { argument := 1937140093240386808077877248, coefficient := (-1937140093240386808077877248) }, { argument := 233234258717906103982620672, coefficient := (-233234258717906103982620672) }, { argument := 100190209473088206520102944768, coefficient := (-100190209473088206520102944768) }, { argument := 233234258717906103982620672, coefficient := (-233234258717906103982620672) }, { argument := 233234258717906103982620672, coefficient := (-233234258717906103982620672) }, { argument := 9990200748416978120588918784, coefficient := (-9990200748416978120588918784) }, { argument := 233234258717906103982620672, coefficient := (-233234258717906103982620672) }, { argument := 1937140093240386808077877248, coefficient := (-1937140093240386808077877248) }, { argument := 9990200748416978120588918784, coefficient := (-9990200748416978120588918784) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16
