import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 12, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4922480665380117550983836587786240)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4687927891, 422998941755481, 15759141127264167, 6450419525, 60633943535, 715996567275,
    50313272295, 7879568687114965, 715996567275, 6450419525, 50313272295, 50313272295,
    50313272295, 50313272295, 50313272295, 211501347394859, 60633943535, 675,
    13527, 22707, 21789, 675, 21789, 14553,
    351, 13527, 81, 10395525, 870408315, 435204315,
    5197605, 249762936157, 26494463885681, 106363896093, 995737159926323, 3506502069,
    8181838161, 106363896093, 106363896093, 3506502069, 1312600607829, 52597531035,
    26494463885681, 106363896093, 8181838161, 52597531035, 8181838161, 106363896093,
    106363896093, 1073786656913, 24256225, 2030952735, 1015476735, 12127745,
    8334775, 615501325, 6415267375, 615501325, 8334775, 115720358985,
    1425, 4272485659575, 22425, 675
  ]
def negativeCoefficients : Array ℕ := #[
    21619251510320491713437630464, 476254469117024593182556422144, 17743215527106490195688143454208, 237978476291468261845683404800, 279624709642475207668678000640, 3301951358544122133108857241600,
    7424928460293809769585322229760, 17743211301565592380209700536320, 3301951358544122133108857241600, 237978476291468261845683404800, 232029014384181555299541319680, 232029014384181555299541319680,
    232029014384181555299541319680, 7424928460293809769585322229760, 232029014384181555299541319680, 476258694657922408660999340032, 279624709642475207668678000640, 12750389503748042076979200,
    255517805655110763222663168, 428923102906084135469580288, 411582573180986798244888576, 12750389503748042076979200, 411582573180986798244888576, 274898397700807787179671552,
    13260405083897963760058368, 255517805655110763222663168, 12240373923598120393900032, 1534108713494795892503347200, 128449595411470132971904696320, 128449641897265198719974768640,
    1534062227699730144433274880, 17997316259322018915734781952, 1909127322926944242124420284416, 245258446238775785143230529536, 17937606009612576980342335864832, 129367092521552062493132587008,
    9433017163029837890124251136, 245258446238775785143230529536, 245258446238775785143230529536, 129367092521552062493132587008, 3026650935452145128745581150208, 242563298477910117174623600640,
    1909127322926944242124420284416, 245258446238775785143230529536, 9433017163029837890124251136, 242563298477910117174623600640, 9433017163029837890124251136, 245258446238775785143230529536,
    245258446238775785143230529536, 19343620751795189730762555392, 111862093692328867161702400, 9366116332086363862534717440, 9366119721675587406664826880, 111858704103105323031592960,
    153749461336952528070246400, 22707990838608253369607782400, 236681590862086963416006656000, 22707990838608253369607782400, 153749461336952528070246400, 4169265324832208229740052480,
    13458744476178488859033600, 153932518595262062603639193600, 105899068378351793917132800, 12750389503748042076979200
  ]
def negativeScales : Array ℕ := #[
    32, 48, 53, 32, 35, 39,
    35, 52, 39, 32, 35, 35,
    35, 35, 35, 47, 35, 9,
    13, 14, 14, 9, 14, 13,
    8, 13, 6, 23, 29, 28,
    22, 37, 44, 36, 49, 31,
    32, 36, 36, 31, 40, 35,
    44, 36, 32, 35, 32, 36,
    36, 39, 24, 30, 29, 23,
    22, 29, 32, 29, 22, 36,
    10, 41, 14, 9
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32126303232599495, 48587647382490908, 53807038429041782, 32586745848162406, 35819406605903476, 39381161714508613,
    35550219972134729, 52807038085464390, 39381161714508613, 32586745848162406, 35550219972134729, 35550219972134729,
    35550219972134729, 35550219972134729, 35550219972134729, 47587660182664450, 35819406605903476, 9398743691938200,
    13723554295483443, 14470849492418713, 14411312365441260, 9398743691938200, 14411312365441260, 13829028966070369,
    8455327220304618, 13723554295483443, 6339850002884626, 23309459283953801, 29697117097868714, 28697117619978681,
    22309415567467788, 37861768448452861, 44590756168345572, 36630217572745224, 49822758300537902, 31707385433340949,
    32929777861969663, 36630217572745224, 36630217572745224, 31707385433340949, 40255565144934355, 35614276028871783,
    44590756168345572, 36630217572745224, 32929777861969663, 35614276028871783, 32929777861969663, 36630217572745224,
    36630217572745224, 39965844535142996, 24531851705291009, 30919509525308549, 29919510047418571, 23531807988804994,
    22990711843434617, 29197186721525726, 32578862249085787, 29197186721525726, 22990711843434617, 36751851747877158,
    10476746203939589, 41958212800177200, 14452820364694038, 9398743691938200
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
noncomputable def negativeCeiling : ℝ := 24592318191 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 21619251510320491713437630464, coefficient := (-21619251510320491713437630464) }, { argument := 476254469117024593182556422144, coefficient := (-476254469117024593182556422144) }, { argument := 17743215527106490195688143454208, coefficient := (-17743215527106490195688143454208) }, { argument := 237978476291468261845683404800, coefficient := (-237978476291468261845683404800) }, { argument := 279624709642475207668678000640, coefficient := (-279624709642475207668678000640) }, { argument := 3301951358544122133108857241600, coefficient := (-3301951358544122133108857241600) }, { argument := 7424928460293809769585322229760, coefficient := (-7424928460293809769585322229760) }, { argument := 17743211301565592380209700536320, coefficient := (-17743211301565592380209700536320) }, { argument := 3301951358544122133108857241600, coefficient := (-3301951358544122133108857241600) }, { argument := 237978476291468261845683404800, coefficient := (-237978476291468261845683404800) }, { argument := 232029014384181555299541319680, coefficient := (-232029014384181555299541319680) }, { argument := 232029014384181555299541319680, coefficient := (-232029014384181555299541319680) }, { argument := 232029014384181555299541319680, coefficient := (-232029014384181555299541319680) }, { argument := 7424928460293809769585322229760, coefficient := (-7424928460293809769585322229760) }, { argument := 232029014384181555299541319680, coefficient := (-232029014384181555299541319680) }, { argument := 476258694657922408660999340032, coefficient := (-476258694657922408660999340032) }, { argument := 279624709642475207668678000640, coefficient := (-279624709642475207668678000640) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 428923102906084135469580288, coefficient := (-428923102906084135469580288) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 274898397700807787179671552, coefficient := (-274898397700807787179671552) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 12240373923598120393900032, coefficient := (-12240373923598120393900032) }, { argument := 1534108713494795892503347200, coefficient := (-1534108713494795892503347200) }, { argument := 128449595411470132971904696320, coefficient := (-128449595411470132971904696320) }, { argument := 128449641897265198719974768640, coefficient := (-128449641897265198719974768640) }, { argument := 1534062227699730144433274880, coefficient := (-1534062227699730144433274880) }, { argument := 17997316259322018915734781952, coefficient := (-17997316259322018915734781952) }, { argument := 1909127322926944242124420284416, coefficient := (-1909127322926944242124420284416) }, { argument := 245258446238775785143230529536, coefficient := (-245258446238775785143230529536) }, { argument := 17937606009612576980342335864832, coefficient := (-17937606009612576980342335864832) }, { argument := 129367092521552062493132587008, coefficient := (-129367092521552062493132587008) }, { argument := 9433017163029837890124251136, coefficient := (-9433017163029837890124251136) }, { argument := 245258446238775785143230529536, coefficient := (-245258446238775785143230529536) }, { argument := 245258446238775785143230529536, coefficient := (-245258446238775785143230529536) }, { argument := 129367092521552062493132587008, coefficient := (-129367092521552062493132587008) }, { argument := 3026650935452145128745581150208, coefficient := (-3026650935452145128745581150208) }, { argument := 242563298477910117174623600640, coefficient := (-242563298477910117174623600640) }, { argument := 1909127322926944242124420284416, coefficient := (-1909127322926944242124420284416) }, { argument := 245258446238775785143230529536, coefficient := (-245258446238775785143230529536) }, { argument := 9433017163029837890124251136, coefficient := (-9433017163029837890124251136) }, { argument := 242563298477910117174623600640, coefficient := (-242563298477910117174623600640) }, { argument := 9433017163029837890124251136, coefficient := (-9433017163029837890124251136) }, { argument := 245258446238775785143230529536, coefficient := (-245258446238775785143230529536) }, { argument := 245258446238775785143230529536, coefficient := (-245258446238775785143230529536) }, { argument := 19343620751795189730762555392, coefficient := (-19343620751795189730762555392) }, { argument := 111862093692328867161702400, coefficient := (-111862093692328867161702400) }, { argument := 9366116332086363862534717440, coefficient := (-9366116332086363862534717440) }, { argument := 9366119721675587406664826880, coefficient := (-9366119721675587406664826880) }, { argument := 111858704103105323031592960, coefficient := (-111858704103105323031592960) }, { argument := 153749461336952528070246400, coefficient := (-153749461336952528070246400) }, { argument := 22707990838608253369607782400, coefficient := (-22707990838608253369607782400) }, { argument := 236681590862086963416006656000, coefficient := (-236681590862086963416006656000) }, { argument := 22707990838608253369607782400, coefficient := (-22707990838608253369607782400) }, { argument := 153749461336952528070246400, coefficient := (-153749461336952528070246400) }, { argument := 4169265324832208229740052480, coefficient := (-4169265324832208229740052480) }, { argument := 13458744476178488859033600, coefficient := (-13458744476178488859033600) }, { argument := 153932518595262062603639193600, coefficient := (-153932518595262062603639193600) }, { argument := 105899068378351793917132800, coefficient := (-105899068378351793917132800) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }] }

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


end Parent1

namespace Parent1

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-99572869016344241916646478839808)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    34179510264705, 675, 675, 57825, 675, 22425,
    57825, 926137883775, 675, 675, 1425, 675,
    13527, 22707, 21789, 675, 21789, 14553,
    351, 13527, 81, 57825, 1158813, 1945233,
    1866591, 57825, 1866591, 1246707, 30069, 1158813,
    6939, 315330925, 26402385555, 13201197555, 157660685, 675,
    13527, 22707, 21789, 675, 21789, 14553,
    351, 13527, 81, 315330925, 26402385555, 13201197555,
    157660685, 78346885, 5785712455, 60303513325, 5785712455, 78346885,
    22425, 449397, 754377, 723879, 22425, 723879,
    483483, 11661, 449397, 2691
  ]
def negativeCoefficients : Array ℕ := #[
    153930829691831481100067143680, 12750389503748042076979200, 12750389503748042076979200, 546141683743874468963942400, 12750389503748042076979200, 105899068378351793917132800,
    546141683743874468963942400, 4170954228262789733312102400, 12750389503748042076979200, 12750389503748042076979200, 13458744476178488859033600, 12750389503748042076979200,
    255517805655110763222663168, 428923102906084135469580288, 411582573180986798244888576, 12750389503748042076979200, 411582573180986798244888576, 274898397700807787179671552,
    13260405083897963760058368, 255517805655110763222663168, 12240373923598120393900032, 546141683743874468963942400, 10944679342227244358037405696, 18372206241143937135947022336,
    17629453551252267858156060672, 546141683743874468963942400, 17629453551252267858156060672, 11774814701517933550862598144, 567987351093629447722500096, 10944679342227244358037405696,
    524296016394119490205384704, 2908414436000550546204262400, 243519024634245460425902653440, 243519112763565272573285498880, 2908326306680738398821416960, 12750389503748042076979200,
    255517805655110763222663168, 428923102906084135469580288, 411582573180986798244888576, 12750389503748042076979200, 411582573180986798244888576, 274898397700807787179671552,
    13260405083897963760058368, 255517805655110763222663168, 12240373923598120393900032, 2908414436000550546204262400, 243519024634245460425902653440, 243519112763565272573285498880,
    2908326306680738398821416960, 180655617070919220482539520, 26681889235364697709289144320, 278100869262952182013807820800, 26681889235364697709289144320, 180655617070919220482539520,
    105899068378351793917132800, 2122217330302169950099341312, 3562444660247754347372347392, 3418421927253195907645046784, 105899068378351793917132800, 3418421927253195907645046784,
    2283183914237264676853383168, 110135031113485865673818112, 2122217330302169950099341312, 101663105643217722160447488
  ]
def negativeScales : Array ℕ := #[
    44, 9, 9, 15, 9, 14,
    15, 39, 9, 9, 10, 9,
    13, 14, 14, 9, 14, 13,
    8, 13, 6, 15, 20, 20,
    20, 15, 20, 20, 14, 20,
    12, 28, 34, 33, 27, 9,
    13, 14, 14, 9, 14, 13,
    8, 13, 6, 28, 34, 33,
    27, 26, 32, 35, 32, 26,
    14, 18, 19, 19, 14, 19,
    18, 13, 18, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    44958196971251119, 9398743691938200, 9398743691938200, 15819405741365596, 9398743691938200, 14452820364694038,
    15819405741365596, 39752436042483347, 9398743691938200, 9398743691938200, 10476746203939589, 9398743691938200,
    13723554295483443, 14470849492418713, 14411312365441260, 9398743691938200, 14411312365441260, 13829028966070369,
    8455327220304618, 13723554295483443, 6339850002884626, 15819405741365596, 20144216343831399, 20891511544639398,
    20831974415136888, 15819405741365596, 20831974415136888, 20249691013388697, 14875989271598903, 20144216343831399,
    12760512051639823, 28232291423431341, 34619949237288353, 33619949759398319, 27232247706945328, 9398743691938200,
    13723554295483443, 14470849492418713, 14411312365441260, 9398743691938200, 14411312365441260, 13829028966070369,
    8455327220304618, 13723554295483443, 6339850002884626, 28232291423431341, 34619949237288353, 33619949759398319,
    27232247706945328, 26223372579823372, 32429847478316023, 35811523006688579, 32429847478316023, 26223372579823372,
    14452820364694038, 18777630968521050, 19524926165175017, 19465389038197124, 14452820364694038, 19465389038197124,
    18883105640887843, 13509403893060724, 18777630968521050, 11393926675640423
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
noncomputable def negativeCeiling : ℝ := 131403929 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 153930829691831481100067143680, coefficient := (-153930829691831481100067143680) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 546141683743874468963942400, coefficient := (-546141683743874468963942400) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 105899068378351793917132800, coefficient := (-105899068378351793917132800) }, { argument := 546141683743874468963942400, coefficient := (-546141683743874468963942400) }, { argument := 4170954228262789733312102400, coefficient := (-4170954228262789733312102400) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 13458744476178488859033600, coefficient := (-13458744476178488859033600) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 428923102906084135469580288, coefficient := (-428923102906084135469580288) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 274898397700807787179671552, coefficient := (-274898397700807787179671552) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 12240373923598120393900032, coefficient := (-12240373923598120393900032) }, { argument := 546141683743874468963942400, coefficient := (-546141683743874468963942400) }, { argument := 10944679342227244358037405696, coefficient := (-10944679342227244358037405696) }, { argument := 18372206241143937135947022336, coefficient := (-18372206241143937135947022336) }, { argument := 17629453551252267858156060672, coefficient := (-17629453551252267858156060672) }, { argument := 546141683743874468963942400, coefficient := (-546141683743874468963942400) }, { argument := 17629453551252267858156060672, coefficient := (-17629453551252267858156060672) }, { argument := 11774814701517933550862598144, coefficient := (-11774814701517933550862598144) }, { argument := 567987351093629447722500096, coefficient := (-567987351093629447722500096) }, { argument := 10944679342227244358037405696, coefficient := (-10944679342227244358037405696) }, { argument := 524296016394119490205384704, coefficient := (-524296016394119490205384704) }, { argument := 2908414436000550546204262400, coefficient := (-2908414436000550546204262400) }, { argument := 243519024634245460425902653440, coefficient := (-243519024634245460425902653440) }, { argument := 243519112763565272573285498880, coefficient := (-243519112763565272573285498880) }, { argument := 2908326306680738398821416960, coefficient := (-2908326306680738398821416960) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 428923102906084135469580288, coefficient := (-428923102906084135469580288) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 274898397700807787179671552, coefficient := (-274898397700807787179671552) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 12240373923598120393900032, coefficient := (-12240373923598120393900032) }, { argument := 2908414436000550546204262400, coefficient := (-2908414436000550546204262400) }, { argument := 243519024634245460425902653440, coefficient := (-243519024634245460425902653440) }, { argument := 243519112763565272573285498880, coefficient := (-243519112763565272573285498880) }, { argument := 2908326306680738398821416960, coefficient := (-2908326306680738398821416960) }, { argument := 180655617070919220482539520, coefficient := (-180655617070919220482539520) }, { argument := 26681889235364697709289144320, coefficient := (-26681889235364697709289144320) }, { argument := 278100869262952182013807820800, coefficient := (-278100869262952182013807820800) }, { argument := 26681889235364697709289144320, coefficient := (-26681889235364697709289144320) }, { argument := 180655617070919220482539520, coefficient := (-180655617070919220482539520) }, { argument := 105899068378351793917132800, coefficient := (-105899068378351793917132800) }, { argument := 2122217330302169950099341312, coefficient := (-2122217330302169950099341312) }, { argument := 3562444660247754347372347392, coefficient := (-3562444660247754347372347392) }, { argument := 3418421927253195907645046784, coefficient := (-3418421927253195907645046784) }, { argument := 105899068378351793917132800, coefficient := (-105899068378351793917132800) }, { argument := 3418421927253195907645046784, coefficient := (-3418421927253195907645046784) }, { argument := 2283183914237264676853383168, coefficient := (-2283183914237264676853383168) }, { argument := 110135031113485865673818112, coefficient := (-110135031113485865673818112) }, { argument := 2122217330302169950099341312, coefficient := (-2122217330302169950099341312) }, { argument := 101663105643217722160447488, coefficient := (-101663105643217722160447488) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk12
