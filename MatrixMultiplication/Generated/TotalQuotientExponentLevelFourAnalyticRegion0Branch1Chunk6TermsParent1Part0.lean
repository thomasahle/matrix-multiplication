import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 0, branch 1,
parent chunk 6, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk6

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
def constantNumerator : ℤ := 10362446108836542233584072654848
def positiveArguments : Array ℕ := #[
    5, 25154259, 25177389, 6589849, 89873351, 26373589,
    1915975, 138758499, 69385627, 3850969, 95367, 3894975,
    5293001, 974669, 49311
  ]
def positiveCoefficients : Array ℕ := #[
    3169126500570573503741758013440, 237575259206044237886839062528, 237793715879541787674424639488, 497914912716352778269269950464, 1697659601862316446143882461184, 498183010906318253767341899776,
    36191744488064673953244774400, 1310536969781802365029982404608, 1310657437350780369679383789568, 36371373864340069517883342848, 900715848743658910189092864, 36786998783230392732431155200,
    399927848259128239771810267136, 36821953739936593846302932992, 931458454547140300530253824
  ]
def positiveScales : Array ℕ := #[
    2, 24, 24, 22, 26, 24,
    20, 27, 26, 21, 16, 21,
    22, 19, 15
  ]
def negativeArguments : Array ℕ := #[
    799636965591, 32658416627055, 44380500247883, 8172362553617, 413465386383, 5935718336965,
    53789702275443, 215177908469847, 745605551619, 5935718336965, 20270180805455, 1484706820795,
    799636965591, 800355792681, 800355792681, 32688420262545, 44421320817333, 8179869787887,
    413835911793, 20270180805455, 733557121997997, 733625886834617, 20371432732747, 53789702275443,
    733557121997997, 215274723679623, 32658416627055, 32688420262545, 1484706820795, 215274723679623,
    13455866010623, 5967992215453, 215177908469847, 733625886834617, 13455866010623, 44380500247883,
    44421320817333, 745605551619, 20371432732747, 5967992215453, 8172362553617, 8179869787887,
    413465386383, 413835911793, 3, 17, 17, 3
  ]
def negativeCoefficients : Array ℕ := #[
    225077796266706358235037696, 9192527059507206802196398080, 99936002189441042079740329984, 9201262237801529084380971008, 232760320005634618866794496, 3341512361316474276628398080,
    121123641562027507797001764864, 121134393550395705540439179264, 3357908884436701520565633024, 3341512361316474276628398080, 11411097340272464809122856960, 3343262542443397890871132160,
    225077796266706358235037696, 225280128105123096859508736, 225280128105123096859508736, 9200972332107989564019179520, 100027921940123077806164803584, 9209714632166767838770495488,
    232968907267935531398332416, 11411097340272464809122856960, 412955947660644095427361112064, 412994658822216348557067157504, 11468097108025314278390104064, 121123641562027507797001764864,
    412955947660644095427361112064, 121188895668229579290628325376, 9192527059507206802196398080, 9200972332107989564019179520, 3343262542443397890871132160, 121188895668229579290628325376,
    121199666302778130742185558016, 3359680939708018959985934336, 121134393550395705540439179264, 412994658822216348557067157504, 121199666302778130742185558016, 99936002189441042079740329984,
    100027921940123077806164803584, 3357908884436701520565633024, 11468097108025314278390104064, 3359680939708018959985934336, 9201262237801529084380971008, 9209714632166767838770495488,
    232760320005634618866794496, 232968907267935531398332416, 475368975085586025561263702016, 2693757525484987478180494311424, 2693757525484987478180494311424, 475368975085586025561263702016
  ]
def negativeScales : Array ℕ := #[
    39, 44, 45, 42, 38, 42,
    45, 47, 39, 42, 44, 40,
    39, 39, 39, 44, 45, 42,
    38, 44, 49, 49, 44, 45,
    49, 47, 44, 44, 40, 47,
    43, 42, 47, 49, 43, 45,
    45, 39, 44, 42, 42, 42,
    38, 38, 1, 4, 4, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    2321928094887362, 24584299355215320, 24585625341546808, 22651813976976898, 26421390059377408, 24652590575199398,
    20869647305811293, 27048000898775232, 26048133508522912, 21876790078746188, 16541202513992974, 21893182637425752,
    22335654495863541, 19894552833428728, 15589621889748028
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    39540554210244385, 44892520083988211, 45334991162924456, 42893890350878920, 38588975601737773, 42432559773143335,
    45612395237214901, 47612523297696402, 39439621645791009, 42432559773143335, 44204424190913288, 40433315214493723,
    39540554210244385, 39541850526546374, 39541850526546374, 44893844894927971, 45336317523950692, 42895215020313764,
    38590267888377513, 44204424190913288, 49381902641171829, 49382037875410850, 44211612682849865, 45612395237214901,
    49381902641171829, 47613172264922899, 44892520083988211, 44893844894927971, 40433315214493723, 47613172264922899,
    43613300478407378, 42440382792416016, 47612523297696402, 49382037875410850, 43613300478407378, 45334991162924456,
    45336317523950692, 39439621645791009, 44211612682849865, 42440382792416016, 42893890350878920, 42895215020313764,
    38588975601737773, 38590267888377513, 1584962500724866, 4087462841250340, 4087462841250340, 1584962500724866
  ]

abbrev PositiveTerm := Fin 15
abbrev NegativeTerm := Fin 48
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
noncomputable def positiveFloor : ℝ := 2035451689 / 1000000000000
noncomputable def negativeCeiling : ℝ := 524693641 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 225077796266706358235037696, coefficient := (-225077796266706358235037696) }, { argument := 9192527059507206802196398080, coefficient := (-9192527059507206802196398080) }, { argument := 99936002189441042079740329984, coefficient := (-99936002189441042079740329984) }, { argument := 9201262237801529084380971008, coefficient := (-9201262237801529084380971008) }, { argument := 232760320005634618866794496, coefficient := (-232760320005634618866794496) }, { argument := 3341512361316474276628398080, coefficient := (-3341512361316474276628398080) }, { argument := 121123641562027507797001764864, coefficient := (-121123641562027507797001764864) }, { argument := 121134393550395705540439179264, coefficient := (-121134393550395705540439179264) }, { argument := 3357908884436701520565633024, coefficient := (-3357908884436701520565633024) }, { argument := 3341512361316474276628398080, coefficient := (-3341512361316474276628398080) }, { argument := 11411097340272464809122856960, coefficient := (-11411097340272464809122856960) }, { argument := 3343262542443397890871132160, coefficient := (-3343262542443397890871132160) }, { argument := 225077796266706358235037696, coefficient := (-225077796266706358235037696) }, { argument := 225280128105123096859508736, coefficient := (-225280128105123096859508736) }, { argument := 225280128105123096859508736, coefficient := (-225280128105123096859508736) }, { argument := 9200972332107989564019179520, coefficient := (-9200972332107989564019179520) }, { argument := 100027921940123077806164803584, coefficient := (-100027921940123077806164803584) }, { argument := 9209714632166767838770495488, coefficient := (-9209714632166767838770495488) }, { argument := 232968907267935531398332416, coefficient := (-232968907267935531398332416) }, { argument := 11411097340272464809122856960, coefficient := (-11411097340272464809122856960) }, { argument := 412955947660644095427361112064, coefficient := (-412955947660644095427361112064) }, { argument := 412994658822216348557067157504, coefficient := (-412994658822216348557067157504) }, { argument := 11468097108025314278390104064, coefficient := (-11468097108025314278390104064) }, { argument := 121123641562027507797001764864, coefficient := (-121123641562027507797001764864) }, { argument := 412955947660644095427361112064, coefficient := (-412955947660644095427361112064) }, { argument := 121188895668229579290628325376, coefficient := (-121188895668229579290628325376) }, { argument := 9192527059507206802196398080, coefficient := (-9192527059507206802196398080) }, { argument := 9200972332107989564019179520, coefficient := (-9200972332107989564019179520) }, { argument := 3343262542443397890871132160, coefficient := (-3343262542443397890871132160) }, { argument := 121188895668229579290628325376, coefficient := (-121188895668229579290628325376) }, { argument := 121199666302778130742185558016, coefficient := (-121199666302778130742185558016) }, { argument := 3359680939708018959985934336, coefficient := (-3359680939708018959985934336) }, { argument := 121134393550395705540439179264, coefficient := (-121134393550395705540439179264) }, { argument := 412994658822216348557067157504, coefficient := (-412994658822216348557067157504) }, { argument := 121199666302778130742185558016, coefficient := (-121199666302778130742185558016) }, { argument := 99936002189441042079740329984, coefficient := (-99936002189441042079740329984) }, { argument := 100027921940123077806164803584, coefficient := (-100027921940123077806164803584) }, { argument := 3357908884436701520565633024, coefficient := (-3357908884436701520565633024) }, { argument := 11468097108025314278390104064, coefficient := (-11468097108025314278390104064) }, { argument := 3359680939708018959985934336, coefficient := (-3359680939708018959985934336) }, { argument := 9201262237801529084380971008, coefficient := (-9201262237801529084380971008) }, { argument := 9209714632166767838770495488, coefficient := (-9209714632166767838770495488) }, { argument := 232760320005634618866794496, coefficient := (-232760320005634618866794496) }, { argument := 232968907267935531398332416, coefficient := (-232968907267935531398332416) }, { argument := 3169126500570573503741758013440, coefficient := 3169126500570573503741758013440 }, { argument := 237575259206044237886839062528, coefficient := 237575259206044237886839062528 }, { argument := 237793715879541787674424639488, coefficient := 237793715879541787674424639488 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 497914912716352778269269950464, coefficient := 497914912716352778269269950464 }, { argument := 1697659601862316446143882461184, coefficient := 1697659601862316446143882461184 }, { argument := 498183010906318253767341899776, coefficient := 498183010906318253767341899776 }, { argument := 2693757525484987478180494311424, coefficient := (-2693757525484987478180494311424) }, { argument := 36191744488064673953244774400, coefficient := 36191744488064673953244774400 }, { argument := 1310536969781802365029982404608, coefficient := 1310536969781802365029982404608 }, { argument := 1310657437350780369679383789568, coefficient := 1310657437350780369679383789568 }, { argument := 36371373864340069517883342848, coefficient := 36371373864340069517883342848 }, { argument := 2693757525484987478180494311424, coefficient := (-2693757525484987478180494311424) }, { argument := 900715848743658910189092864, coefficient := 900715848743658910189092864 }, { argument := 36786998783230392732431155200, coefficient := 36786998783230392732431155200 }, { argument := 399927848259128239771810267136, coefficient := 399927848259128239771810267136 }, { argument := 36821953739936593846302932992, coefficient := 36821953739936593846302932992 }, { argument := 931458454547140300530253824, coefficient := 931458454547140300530253824 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region0.Branch1.Chunk6
