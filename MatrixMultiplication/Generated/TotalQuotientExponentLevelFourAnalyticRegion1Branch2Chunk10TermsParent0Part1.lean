import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 10, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10

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
def constantNumerator : ℤ := (-43803478046176430111131294867914752)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    19930621131, 57683392135797, 20783561751, 1846228077, 351197287965525, 22151471520802987,
    81065675535, 83220001185, 2272001434869, 1700960603079, 1384467114052443, 2272001434869,
    81065675535, 80078850597, 18534259863, 80078850597, 1700960603079, 18534259863,
    21949686495589, 83220001185, 1385641565123899, 190716183400994537, 69927, 1982611943192786505,
    27369, 4965, 69927, 54483, 27369, 994659,
    28107, 95358107874771059, 69927, 4965, 28107, 4965,
    70161, 54483, 1385621563391149, 103803, 546795, 1644357,
    54045, 72063, 119865, 1644357, 1397253, 72063,
    22399869, 709587, 546795, 1644357, 119865, 709587,
    119865, 1648101, 1397253, 57789, 1205612971397195, 44589880738251701,
    89175940980588171, 2415046472112501, 5151, 29715
  ]
def negativeCoefficients : Array ℕ := #[
    183827533616812305497192398848, 129891451664120784300231622656, 191694522280417880824828919808, 8514224209528982934134980608, 790825987607533584630625075200, 49880679443398243293128636235776,
    186924721219565329391623864320, 191892257959187576603667333120, 5238878625516165446387827212288, 3922148115557621018179254878208, 49880684631626306249013879373824, 5238878625516165446387827212288,
    186924721219565329391623864320, 184649257834960292428690489344, 170948374144194028018077794304, 184649257834960292428690489344, 3922148115557621018179254878208, 170948374144194028018077794304,
    790820799379470628745381937152, 191892257959187576603667333120, 390023427272566400156113567744, 53681833281140135709223285686272, 1320883684190502723432480768, 558055650536458017969611766497280,
    1033971586157274558829166592, 46893099174895576972001280, 1320883684190502723432480768, 1029154772344747520711196672, 1033971586157274558829166592, 18788577293938553754438598656,
    1061852437872136944170827776, 53681842386446812694745771409408, 1320883684190502723432480768, 46893099174895576972001280, 1061852437872136944170827776, 46893099174895576972001280,
    1325303819218468711352500224, 1029154772344747520711196672, 390017797285306421140724383744, 980391616042635564234571776, 20657331048005661236983234560, 31061025530688324778630053888,
    1020881186266759902296801280, 21779705334722255554212790272, 1132092916938340047079342080, 31061025530688324778630053888, 26393362941156241535089508352, 21779705334722255554212790272,
    423121562345083187453069623296, 26807438923840183506007228416, 20657331048005661236983234560, 31061025530688324778630053888, 1132092916938340047079342080, 26807438923840183506007228416,
    1132092916938340047079342080, 31131747691135780585350365184, 26393362941156241535089508352, 1091603346714215709017112576, 1357399532184360963574260039680, 50203742569321304427428707303424,
    50201591821323778823219526500352, 1359550298986036307921115021312, 48649819506523084991496192, 1122600960307772060199813120
  ]
def negativeScales : Array ℕ := #[
    34, 45, 34, 30, 48, 54,
    36, 36, 41, 40, 50, 41,
    36, 36, 34, 36, 40, 34,
    44, 36, 50, 57, 16, 60,
    14, 12, 16, 15, 14, 19,
    14, 56, 16, 12, 14, 12,
    16, 15, 50, 16, 19, 20,
    15, 16, 16, 20, 20, 16,
    24, 19, 19, 20, 16, 19,
    16, 20, 20, 15, 50, 55,
    56, 51, 12, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    34214267620849387, 45713221239988187, 34274723863951956, 30781933644268308, 48319275032482578, 54298252058298614,
    36238372133135290, 36276211257799358, 41047100884616708, 40629486864964486, 50298252208357326, 41047100884616708,
    36238372133135290, 36220702215631088, 34109475453385993, 36220702215631088, 40629486864964486, 34109475453385993,
    44319265567624862, 36276211257799358, 50299475535695214, 57404204883173884, 16093561991730624, 60782108034792065,
    14740255102654583, 12277578002415737, 16093561991730624, 15733518524427902, 14740255102654583, 19923842490840912,
    14778641855878192, 56404205127878263, 16093561991730624, 12277578002415737, 14778641855878192, 12277578002415737,
    16098381690113731, 15733518524427902, 50299454710245367, 16663488613948452, 19060640525156599, 20649092120320883,
    15721873532155397, 16136971092305436, 16871050937283783, 20649092120320883, 20414161841895461, 16136971092305436,
    24416986959280010, 19436620053400322, 19060640525156599, 20649092120320883, 16871050937283783, 19436620053400322,
    16871050937283783, 20652373226755207, 20414161841895461, 15818507285743830, 50098688267646247, 55307565859169128,
    56307504052224516, 51100972374044849, 12330636824723291, 14858903762549026
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
noncomputable def negativeCeiling : ℝ := 625174716353 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 183827533616812305497192398848, coefficient := (-183827533616812305497192398848) }, { argument := 129891451664120784300231622656, coefficient := (-129891451664120784300231622656) }, { argument := 191694522280417880824828919808, coefficient := (-191694522280417880824828919808) }, { argument := 8514224209528982934134980608, coefficient := (-8514224209528982934134980608) }, { argument := 790825987607533584630625075200, coefficient := (-790825987607533584630625075200) }, { argument := 49880679443398243293128636235776, coefficient := (-49880679443398243293128636235776) }, { argument := 186924721219565329391623864320, coefficient := (-186924721219565329391623864320) }, { argument := 191892257959187576603667333120, coefficient := (-191892257959187576603667333120) }, { argument := 5238878625516165446387827212288, coefficient := (-5238878625516165446387827212288) }, { argument := 3922148115557621018179254878208, coefficient := (-3922148115557621018179254878208) }, { argument := 49880684631626306249013879373824, coefficient := (-49880684631626306249013879373824) }, { argument := 5238878625516165446387827212288, coefficient := (-5238878625516165446387827212288) }, { argument := 186924721219565329391623864320, coefficient := (-186924721219565329391623864320) }, { argument := 184649257834960292428690489344, coefficient := (-184649257834960292428690489344) }, { argument := 170948374144194028018077794304, coefficient := (-170948374144194028018077794304) }, { argument := 184649257834960292428690489344, coefficient := (-184649257834960292428690489344) }, { argument := 3922148115557621018179254878208, coefficient := (-3922148115557621018179254878208) }, { argument := 170948374144194028018077794304, coefficient := (-170948374144194028018077794304) }, { argument := 790820799379470628745381937152, coefficient := (-790820799379470628745381937152) }, { argument := 191892257959187576603667333120, coefficient := (-191892257959187576603667333120) }, { argument := 390023427272566400156113567744, coefficient := (-390023427272566400156113567744) }, { argument := 53681833281140135709223285686272, coefficient := (-53681833281140135709223285686272) }, { argument := 1320883684190502723432480768, coefficient := (-1320883684190502723432480768) }, { argument := 558055650536458017969611766497280, coefficient := (-558055650536458017969611766497280) }, { argument := 1033971586157274558829166592, coefficient := (-1033971586157274558829166592) }, { argument := 46893099174895576972001280, coefficient := (-46893099174895576972001280) }, { argument := 1320883684190502723432480768, coefficient := (-1320883684190502723432480768) }, { argument := 1029154772344747520711196672, coefficient := (-1029154772344747520711196672) }, { argument := 1033971586157274558829166592, coefficient := (-1033971586157274558829166592) }, { argument := 18788577293938553754438598656, coefficient := (-18788577293938553754438598656) }, { argument := 1061852437872136944170827776, coefficient := (-1061852437872136944170827776) }, { argument := 53681842386446812694745771409408, coefficient := (-53681842386446812694745771409408) }, { argument := 1320883684190502723432480768, coefficient := (-1320883684190502723432480768) }, { argument := 46893099174895576972001280, coefficient := (-46893099174895576972001280) }, { argument := 1061852437872136944170827776, coefficient := (-1061852437872136944170827776) }, { argument := 46893099174895576972001280, coefficient := (-46893099174895576972001280) }, { argument := 1325303819218468711352500224, coefficient := (-1325303819218468711352500224) }, { argument := 1029154772344747520711196672, coefficient := (-1029154772344747520711196672) }, { argument := 390017797285306421140724383744, coefficient := (-390017797285306421140724383744) }, { argument := 980391616042635564234571776, coefficient := (-980391616042635564234571776) }, { argument := 20657331048005661236983234560, coefficient := (-20657331048005661236983234560) }, { argument := 31061025530688324778630053888, coefficient := (-31061025530688324778630053888) }, { argument := 1020881186266759902296801280, coefficient := (-1020881186266759902296801280) }, { argument := 21779705334722255554212790272, coefficient := (-21779705334722255554212790272) }, { argument := 1132092916938340047079342080, coefficient := (-1132092916938340047079342080) }, { argument := 31061025530688324778630053888, coefficient := (-31061025530688324778630053888) }, { argument := 26393362941156241535089508352, coefficient := (-26393362941156241535089508352) }, { argument := 21779705334722255554212790272, coefficient := (-21779705334722255554212790272) }, { argument := 423121562345083187453069623296, coefficient := (-423121562345083187453069623296) }, { argument := 26807438923840183506007228416, coefficient := (-26807438923840183506007228416) }, { argument := 20657331048005661236983234560, coefficient := (-20657331048005661236983234560) }, { argument := 31061025530688324778630053888, coefficient := (-31061025530688324778630053888) }, { argument := 1132092916938340047079342080, coefficient := (-1132092916938340047079342080) }, { argument := 26807438923840183506007228416, coefficient := (-26807438923840183506007228416) }, { argument := 1132092916938340047079342080, coefficient := (-1132092916938340047079342080) }, { argument := 31131747691135780585350365184, coefficient := (-31131747691135780585350365184) }, { argument := 26393362941156241535089508352, coefficient := (-26393362941156241535089508352) }, { argument := 1091603346714215709017112576, coefficient := (-1091603346714215709017112576) }, { argument := 1357399532184360963574260039680, coefficient := (-1357399532184360963574260039680) }, { argument := 50203742569321304427428707303424, coefficient := (-50203742569321304427428707303424) }, { argument := 50201591821323778823219526500352, coefficient := (-50201591821323778823219526500352) }, { argument := 1359550298986036307921115021312, coefficient := (-1359550298986036307921115021312) }, { argument := 48649819506523084991496192, coefficient := (-48649819506523084991496192) }, { argument := 1122600960307772060199813120, coefficient := (-1122600960307772060199813120) }] }

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
def constantNumerator : ℤ := (-209147476307330874875979476500480)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    37947, 1245, 60861, 5355, 37947, 14469,
    60861, 136281, 29979, 29715, 37947, 5355,
    29979, 5355, 76167, 14469, 2763, 553057955,
    1243713485, 79597671495, 2212232685, 29076562157445, 49981466042491, 29076562157445,
    142551, 808815, 2130219, 69915, 832593, 151305,
    2130219, 1661751, 832593, 30283623, 857079, 808815,
    2130219, 151305, 857079, 151305, 2137317, 1661751,
    77013, 117801, 704865, 1679769, 55065, 713793,
    116655, 1679769, 1211301, 713793, 24724773, 634329,
    704865, 1679769, 116655, 634329, 116655, 1686867,
    1211301, 62163, 4547100911, 81495083557
  ]
def negativeCoefficients : Array ℕ := #[
    1433597127403635415392976896, 47034770169381666328412160, 1149631786055717909403009024, 50576545031533900238684160, 1433597127403635415392976896, 1093246730250254345551478784,
    1149631786055717909403009024, 20594202452862659819766546432, 1132574598319592750891139072, 1122600960307772060199813120, 1433597127403635415392976896, 50576545031533900238684160,
    1132574598319592750891139072, 50576545031533900238684160, 1438753951602929067966332928, 1093246730250254345551478784, 52191594368675318901768192, 5101059276907086940355952640,
    183539714870531226544981934080, 183539734366433869446764298240, 5101061271461289910201221120, 130949194497484367246099742720, 450193023688787133987471491072, 130949194497484367246099742720,
    1346356128999101589715156992, 30556166774737696748124241920, 40238699227088371029897117696, 1320657010599324980462223360, 31454474216575092139254349824, 1429035321381183338116546560,
    40238699227088371029897117696, 31389588901100463214018166784, 31454474216575092139254349824, 572041464940241175181296402432, 32379529142171461200874831872, 30556166774737696748124241920,
    40238699227088371029897117696, 1429035321381183338116546560, 32379529142171461200874831872, 1429035321381183338116546560, 40372776656270005996804374528, 31389588901100463214018166784,
    1454734439780959947369480192, 1112598988097054151637204992, 26629046807583299788414648320, 31729939298253844283859664896, 1040148441516868054768680960, 26966337111255781328157671424,
    1101775324118316924807413760, 31729939298253844283859664896, 22880828972265936467980713984, 26966337111255781328157671424, 467037757247041465996680364032, 23964272069697753430068559872,
    26629046807583299788414648320, 31729939298253844283859664896, 1101775324118316924807413760, 23964272069697753430068559872, 1101775324118316924807413760, 31864016727435479250766921728,
    22880828972265936467980713984, 1174225870698503021675937792, 5242450423909284581407195136, 187914868705194309486865547264
  ]
def negativeScales : Array ℕ := #[
    15, 10, 15, 12, 15, 13,
    15, 17, 14, 14, 15, 12,
    14, 12, 16, 13, 11, 29,
    30, 36, 31, 44, 45, 44,
    17, 19, 21, 16, 19, 17,
    21, 20, 19, 24, 19, 19,
    21, 17, 19, 17, 21, 20,
    16, 16, 19, 20, 15, 19,
    16, 20, 20, 19, 24, 19,
    19, 20, 16, 19, 16, 20,
    20, 15, 32, 36
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15211698213643360, 10281930026955444, 15893230422217317, 12386670859637623, 15211698213643360, 13820677596462139,
    15893230422217317, 17056224913201407, 14871664642721115, 14858903762549026, 15211698213643360, 12386670859637623,
    14871664642721115, 12386670859637623, 16216878452749041, 13820677596462139, 11432019846812516, 29042855427642279,
    30212007023234312, 36212007176479840, 31042855991747250, 44724921937186004, 45506458452311847, 44724921937186004,
    17121118634301809, 19625450227654563, 21022570325584000, 16093314393147463, 19667251903584665, 17207100137840871,
    21022570325584000, 20664272791428176, 19667251903584665, 24852034479376090, 19709068663292793, 19625450227654563,
    21022570325584000, 17207100137840871, 19709068663292793, 17207100137840871, 21027369469091250, 20664272791428176,
    16232814376688060, 16845992262144210, 19426987444741877, 20679831418165570, 15748847994927351, 19445146227722351,
    16831888620276083, 20679831418165570, 20208125978740077, 19445146227722351, 24559453939766844, 19274871774671289,
    19426987444741877, 20679831418165570, 16831888620276083, 19274871774671289, 16831888620276083, 20685914799074640,
    20208125978740077, 15923768516401456, 32082299875263312, 36245993975801609
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
noncomputable def negativeCeiling : ℝ := 1121032357 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1433597127403635415392976896, coefficient := (-1433597127403635415392976896) }, { argument := 47034770169381666328412160, coefficient := (-47034770169381666328412160) }, { argument := 1149631786055717909403009024, coefficient := (-1149631786055717909403009024) }, { argument := 50576545031533900238684160, coefficient := (-50576545031533900238684160) }, { argument := 1433597127403635415392976896, coefficient := (-1433597127403635415392976896) }, { argument := 1093246730250254345551478784, coefficient := (-1093246730250254345551478784) }, { argument := 1149631786055717909403009024, coefficient := (-1149631786055717909403009024) }, { argument := 20594202452862659819766546432, coefficient := (-20594202452862659819766546432) }, { argument := 1132574598319592750891139072, coefficient := (-1132574598319592750891139072) }, { argument := 1122600960307772060199813120, coefficient := (-1122600960307772060199813120) }, { argument := 1433597127403635415392976896, coefficient := (-1433597127403635415392976896) }, { argument := 50576545031533900238684160, coefficient := (-50576545031533900238684160) }, { argument := 1132574598319592750891139072, coefficient := (-1132574598319592750891139072) }, { argument := 50576545031533900238684160, coefficient := (-50576545031533900238684160) }, { argument := 1438753951602929067966332928, coefficient := (-1438753951602929067966332928) }, { argument := 1093246730250254345551478784, coefficient := (-1093246730250254345551478784) }, { argument := 52191594368675318901768192, coefficient := (-52191594368675318901768192) }, { argument := 5101059276907086940355952640, coefficient := (-5101059276907086940355952640) }, { argument := 183539714870531226544981934080, coefficient := (-183539714870531226544981934080) }, { argument := 183539734366433869446764298240, coefficient := (-183539734366433869446764298240) }, { argument := 5101061271461289910201221120, coefficient := (-5101061271461289910201221120) }, { argument := 130949194497484367246099742720, coefficient := (-130949194497484367246099742720) }, { argument := 450193023688787133987471491072, coefficient := (-450193023688787133987471491072) }, { argument := 130949194497484367246099742720, coefficient := (-130949194497484367246099742720) }, { argument := 1346356128999101589715156992, coefficient := (-1346356128999101589715156992) }, { argument := 30556166774737696748124241920, coefficient := (-30556166774737696748124241920) }, { argument := 40238699227088371029897117696, coefficient := (-40238699227088371029897117696) }, { argument := 1320657010599324980462223360, coefficient := (-1320657010599324980462223360) }, { argument := 31454474216575092139254349824, coefficient := (-31454474216575092139254349824) }, { argument := 1429035321381183338116546560, coefficient := (-1429035321381183338116546560) }, { argument := 40238699227088371029897117696, coefficient := (-40238699227088371029897117696) }, { argument := 31389588901100463214018166784, coefficient := (-31389588901100463214018166784) }, { argument := 31454474216575092139254349824, coefficient := (-31454474216575092139254349824) }, { argument := 572041464940241175181296402432, coefficient := (-572041464940241175181296402432) }, { argument := 32379529142171461200874831872, coefficient := (-32379529142171461200874831872) }, { argument := 30556166774737696748124241920, coefficient := (-30556166774737696748124241920) }, { argument := 40238699227088371029897117696, coefficient := (-40238699227088371029897117696) }, { argument := 1429035321381183338116546560, coefficient := (-1429035321381183338116546560) }, { argument := 32379529142171461200874831872, coefficient := (-32379529142171461200874831872) }, { argument := 1429035321381183338116546560, coefficient := (-1429035321381183338116546560) }, { argument := 40372776656270005996804374528, coefficient := (-40372776656270005996804374528) }, { argument := 31389588901100463214018166784, coefficient := (-31389588901100463214018166784) }, { argument := 1454734439780959947369480192, coefficient := (-1454734439780959947369480192) }, { argument := 1112598988097054151637204992, coefficient := (-1112598988097054151637204992) }, { argument := 26629046807583299788414648320, coefficient := (-26629046807583299788414648320) }, { argument := 31729939298253844283859664896, coefficient := (-31729939298253844283859664896) }, { argument := 1040148441516868054768680960, coefficient := (-1040148441516868054768680960) }, { argument := 26966337111255781328157671424, coefficient := (-26966337111255781328157671424) }, { argument := 1101775324118316924807413760, coefficient := (-1101775324118316924807413760) }, { argument := 31729939298253844283859664896, coefficient := (-31729939298253844283859664896) }, { argument := 22880828972265936467980713984, coefficient := (-22880828972265936467980713984) }, { argument := 26966337111255781328157671424, coefficient := (-26966337111255781328157671424) }, { argument := 467037757247041465996680364032, coefficient := (-467037757247041465996680364032) }, { argument := 23964272069697753430068559872, coefficient := (-23964272069697753430068559872) }, { argument := 26629046807583299788414648320, coefficient := (-26629046807583299788414648320) }, { argument := 31729939298253844283859664896, coefficient := (-31729939298253844283859664896) }, { argument := 1101775324118316924807413760, coefficient := (-1101775324118316924807413760) }, { argument := 23964272069697753430068559872, coefficient := (-23964272069697753430068559872) }, { argument := 1101775324118316924807413760, coefficient := (-1101775324118316924807413760) }, { argument := 31864016727435479250766921728, coefficient := (-31864016727435479250766921728) }, { argument := 22880828972265936467980713984, coefficient := (-22880828972265936467980713984) }, { argument := 1174225870698503021675937792, coefficient := (-1174225870698503021675937792) }, { argument := 5242450423909284581407195136, coefficient := (-5242450423909284581407195136) }, { argument := 187914868705194309486865547264, coefficient := (-187914868705194309486865547264) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
