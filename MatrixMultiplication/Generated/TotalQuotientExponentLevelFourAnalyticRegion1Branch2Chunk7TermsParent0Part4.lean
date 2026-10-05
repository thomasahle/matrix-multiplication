import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 7, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-41564242032486332444894736416768)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1365, 1365, 1365, 1365, 1365, 1575,
    1645, 14880981, 1467575385, 340119, 51330882795, 349011,
    11115, 340119, 193401, 349011, 5448573, 6669,
    1467575385, 340119, 11115, 6669, 11115, 171171,
    193401, 59520249, 630000621, 11584239719, 11583623393, 631234947,
    24255, 18865, 2695, 25333, 299145, 21021,
    18865, 299145, 2695, 21021, 21021, 21021,
    21021, 21021, 24255, 25333, 32445937, 3363639845,
    340119, 119764472015, 349011, 11115, 340119, 193401,
    349011, 5448573, 6669, 3363639845, 340119, 11115,
    6669, 11115, 171171, 193401
  ]
def negativeCoefficients : Array ℕ := #[
    51568241992936525733560320, 51568241992936525733560320, 51568241992936525733560320, 1650183743773968823473930240, 51568241992936525733560320, 59501817684157529692569600,
    62146342914564531012239360, 137252824036367218558107648, 13535993767985381795514286080, 1606166565787140860437069824, 118360957249618229359112355840, 1648157848552817745677254656,
    52489103457096106550231040, 1606166565787140860437069824, 913310400153472253974020096, 1648157848552817745677254656, 25730158514668511430923255808, 1007790786376245245764435968,
    13535993767985381795514286080, 1606166565787140860437069824, 52489103457096106550231040, 1007790786376245245764435968, 52489103457096106550231040, 1616664386478560081747116032,
    913310400153472253974020096, 137244350063308358232834048, 726341263866567955731972096, 26711438173111756437468479488, 26710017022113259798329819136, 727764344855663306732470272,
    1832655984672051914531143680, 1425399099189373711302000640, 1629027541930712812916572160, 1914107361768587555176972288, 22602757144288640279217438720, 50825659308238239762997051392,
    1425399099189373711302000640, 22602757144288640279217438720, 1629027541930712812916572160, 1588301853382444992593657856, 1588301853382444992593657856, 1588301853382444992593657856,
    50825659308238239762997051392, 1588301853382444992593657856, 1832655984672051914531143680, 1914107361768587555176972288, 149630474017675867007746048, 15512050844211766193165434880,
    1606166565787140860437069824, 138079035273978418234539376640, 1648157848552817745677254656, 52489103457096106550231040, 1606166565787140860437069824, 913310400153472253974020096,
    1648157848552817745677254656, 25730158514668511430923255808, 1007790786376245245764435968, 15512050844211766193165434880, 1606166565787140860437069824, 52489103457096106550231040,
    1007790786376245245764435968, 52489103457096106550231040, 1616664386478560081747116032, 913310400153472253974020096
  ]
def negativeScales : Array ℕ := #[
    10, 10, 10, 10, 10, 10,
    10, 23, 30, 18, 35, 18,
    13, 18, 17, 18, 22, 12,
    30, 18, 13, 12, 13, 17,
    17, 25, 29, 33, 33, 29,
    14, 14, 11, 14, 18, 14,
    14, 18, 11, 14, 14, 14,
    14, 14, 14, 14, 24, 31,
    18, 36, 18, 13, 18, 17,
    18, 22, 12, 31, 18, 13,
    12, 13, 17, 17
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    10414685235807227, 10414685235807227, 10414685235807227, 10414685235807227, 10414685235807227, 10621136113284685,
    10683871868671904, 23826966301791860, 30450787466195458, 18375680075719645, 35579108021289978, 18412912981918629,
    13440220327914385, 18375680075719645, 17561235728877581, 18412912981918629, 22377447001893833, 12703254733826280,
    30450787466195458, 18375680075719645, 13440220327914385, 12703254733826280, 13440220327914385, 17385078773721895,
    17561235728877581, 25826877227219643, 29230778009795864, 33431444311192809, 33431367552239280, 29233601838448890,
    14565994559084324, 14203424479697473, 11396069557639874, 14628730314442427, 18190485423989974, 14359543681614756,
    14203424479697473, 18190485423989974, 11396069557639874, 14359543681614756, 14359543681614756, 14359543681614756,
    14359543681614756, 14359543681614756, 14565994559084324, 14628730314442427, 24951534504845379, 31647376094186436,
    18375680075719645, 36801409042289233, 18412912981918629, 13440220327914385, 18375680075719645, 17561235728877581,
    18412912981918629, 22377447001893833, 12703254733826280, 31647376094186436, 18375680075719645, 13440220327914385,
    12703254733826280, 13440220327914385, 17385078773721895, 17561235728877581
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
noncomputable def negativeCeiling : ℝ := 10318511 / 50000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 51568241992936525733560320, coefficient := (-51568241992936525733560320) }, { argument := 51568241992936525733560320, coefficient := (-51568241992936525733560320) }, { argument := 51568241992936525733560320, coefficient := (-51568241992936525733560320) }, { argument := 1650183743773968823473930240, coefficient := (-1650183743773968823473930240) }, { argument := 51568241992936525733560320, coefficient := (-51568241992936525733560320) }, { argument := 59501817684157529692569600, coefficient := (-59501817684157529692569600) }, { argument := 62146342914564531012239360, coefficient := (-62146342914564531012239360) }, { argument := 137252824036367218558107648, coefficient := (-137252824036367218558107648) }, { argument := 13535993767985381795514286080, coefficient := (-13535993767985381795514286080) }, { argument := 1606166565787140860437069824, coefficient := (-1606166565787140860437069824) }, { argument := 118360957249618229359112355840, coefficient := (-118360957249618229359112355840) }, { argument := 1648157848552817745677254656, coefficient := (-1648157848552817745677254656) }, { argument := 52489103457096106550231040, coefficient := (-52489103457096106550231040) }, { argument := 1606166565787140860437069824, coefficient := (-1606166565787140860437069824) }, { argument := 913310400153472253974020096, coefficient := (-913310400153472253974020096) }, { argument := 1648157848552817745677254656, coefficient := (-1648157848552817745677254656) }, { argument := 25730158514668511430923255808, coefficient := (-25730158514668511430923255808) }, { argument := 1007790786376245245764435968, coefficient := (-1007790786376245245764435968) }, { argument := 13535993767985381795514286080, coefficient := (-13535993767985381795514286080) }, { argument := 1606166565787140860437069824, coefficient := (-1606166565787140860437069824) }, { argument := 52489103457096106550231040, coefficient := (-52489103457096106550231040) }, { argument := 1007790786376245245764435968, coefficient := (-1007790786376245245764435968) }, { argument := 52489103457096106550231040, coefficient := (-52489103457096106550231040) }, { argument := 1616664386478560081747116032, coefficient := (-1616664386478560081747116032) }, { argument := 913310400153472253974020096, coefficient := (-913310400153472253974020096) }, { argument := 137244350063308358232834048, coefficient := (-137244350063308358232834048) }, { argument := 726341263866567955731972096, coefficient := (-726341263866567955731972096) }, { argument := 26711438173111756437468479488, coefficient := (-26711438173111756437468479488) }, { argument := 26710017022113259798329819136, coefficient := (-26710017022113259798329819136) }, { argument := 727764344855663306732470272, coefficient := (-727764344855663306732470272) }, { argument := 1832655984672051914531143680, coefficient := (-1832655984672051914531143680) }, { argument := 1425399099189373711302000640, coefficient := (-1425399099189373711302000640) }, { argument := 1629027541930712812916572160, coefficient := (-1629027541930712812916572160) }, { argument := 1914107361768587555176972288, coefficient := (-1914107361768587555176972288) }, { argument := 22602757144288640279217438720, coefficient := (-22602757144288640279217438720) }, { argument := 50825659308238239762997051392, coefficient := (-50825659308238239762997051392) }, { argument := 1425399099189373711302000640, coefficient := (-1425399099189373711302000640) }, { argument := 22602757144288640279217438720, coefficient := (-22602757144288640279217438720) }, { argument := 1629027541930712812916572160, coefficient := (-1629027541930712812916572160) }, { argument := 1588301853382444992593657856, coefficient := (-1588301853382444992593657856) }, { argument := 1588301853382444992593657856, coefficient := (-1588301853382444992593657856) }, { argument := 1588301853382444992593657856, coefficient := (-1588301853382444992593657856) }, { argument := 50825659308238239762997051392, coefficient := (-50825659308238239762997051392) }, { argument := 1588301853382444992593657856, coefficient := (-1588301853382444992593657856) }, { argument := 1832655984672051914531143680, coefficient := (-1832655984672051914531143680) }, { argument := 1914107361768587555176972288, coefficient := (-1914107361768587555176972288) }, { argument := 149630474017675867007746048, coefficient := (-149630474017675867007746048) }, { argument := 15512050844211766193165434880, coefficient := (-15512050844211766193165434880) }, { argument := 1606166565787140860437069824, coefficient := (-1606166565787140860437069824) }, { argument := 138079035273978418234539376640, coefficient := (-138079035273978418234539376640) }, { argument := 1648157848552817745677254656, coefficient := (-1648157848552817745677254656) }, { argument := 52489103457096106550231040, coefficient := (-52489103457096106550231040) }, { argument := 1606166565787140860437069824, coefficient := (-1606166565787140860437069824) }, { argument := 913310400153472253974020096, coefficient := (-913310400153472253974020096) }, { argument := 1648157848552817745677254656, coefficient := (-1648157848552817745677254656) }, { argument := 25730158514668511430923255808, coefficient := (-25730158514668511430923255808) }, { argument := 1007790786376245245764435968, coefficient := (-1007790786376245245764435968) }, { argument := 15512050844211766193165434880, coefficient := (-15512050844211766193165434880) }, { argument := 1606166565787140860437069824, coefficient := (-1606166565787140860437069824) }, { argument := 52489103457096106550231040, coefficient := (-52489103457096106550231040) }, { argument := 1007790786376245245764435968, coefficient := (-1007790786376245245764435968) }, { argument := 52489103457096106550231040, coefficient := (-52489103457096106550231040) }, { argument := 1616664386478560081747116032, coefficient := (-1616664386478560081747116032) }, { argument := 913310400153472253974020096, coefficient := (-913310400153472253974020096) }] }

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

namespace Parent0

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-410483276893779870588712375025664)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    129775173, 27405, 21315, 3045, 28623, 337995,
    23751, 21315, 337995, 3045, 23751, 23751,
    23751, 23751, 23751, 27405, 28623, 649093609,
    45505559165, 340119, 1352570672855, 349011, 11115, 340119,
    193401, 349011, 5448573, 6669, 45505559165, 340119,
    11115, 6669, 11115, 171171, 193401, 2596277661,
    18085936473, 334558601067, 334538686749, 18125799831, 14880981, 1467575385,
    340119, 51330882795, 349011, 11115, 340119, 193401,
    349011, 5448573, 6669, 1467575385, 340119, 11115,
    6669, 11115, 171171, 193401, 59520249, 6721063353,
    123647183387, 123640538789, 6734369991, 3848437131
  ]
def negativeCoefficients : Array ℕ := #[
    149620587715773863294926848, 1035331627704341016650711040, 805257932658931901839441920, 920294780181636459245076480, 1081346366713422839612964864, 12769090075020205872025436160,
    28713197141667057528446386176, 805257932658931901839441920, 12769090075020205872025436160, 920294780181636459245076480, 897287410677095547763949568, 897287410677095547763949568,
    897287410677095547763949568, 28713197141667057528446386176, 897287410677095547763949568, 1035331627704341016650711040, 1081346366713422839612964864, 2993415921275873719050305536,
    209857350961950780521877340160, 51397330105188507533986234368, 1559407815235081996568342036480, 52741051153690167861672148992, 1679651310627075409607393280, 51397330105188507533986234368,
    29225932804911112127168643072, 52741051153690167861672148992, 823365072469392365789544185856, 32249305164039847864461950976, 209857350961950780521877340160, 51397330105188507533986234368,
    1679651310627075409607393280, 32249305164039847864461950976, 1679651310627075409607393280, 51733260367313922615907713024, 29225932804911112127168643072, 2993304347297265391434203136,
    20851665090675011248768155648, 771439611442655040240598646784, 771393692151711481809283842048, 20897624413359052639023661056, 137252824036367218558107648, 13535993767985381795514286080,
    1606166565787140860437069824, 118360957249618229359112355840, 1648157848552817745677254656, 52489103457096106550231040, 1606166565787140860437069824, 913310400153472253974020096,
    1648157848552817745677254656, 25730158514668511430923255808, 1007790786376245245764435968, 13535993767985381795514286080, 1606166565787140860437069824, 52489103457096106550231040,
    1007790786376245245764435968, 52489103457096106550231040, 1616664386478560081747116032, 913310400153472253974020096, 137244350063308358232834048, 15497716946997399766544941056,
    570221986843755093509273550848, 570191344044060422924461408256, 15528399965205837056606994432, 70991134839318039348375453696
  ]
def negativeScales : Array ℕ := #[
    26, 14, 14, 11, 14, 18,
    14, 14, 18, 11, 14, 14,
    14, 14, 14, 14, 14, 29,
    35, 18, 40, 18, 13, 18,
    17, 18, 22, 12, 35, 18,
    13, 12, 13, 17, 17, 31,
    34, 38, 38, 34, 23, 30,
    18, 35, 18, 13, 18, 17,
    18, 22, 12, 30, 18, 13,
    12, 13, 17, 17, 25, 32,
    36, 36, 32, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    26951439180730442, 14742151514425259, 14379581434851302, 11572226512796267, 14804887270297456, 18366642379143803,
    14535700636769438, 14379581434851302, 18366642379143803, 11572226512796267, 14535700636769438, 14535700636769438,
    14535700636769438, 14535700636769438, 14535700636769438, 14742151514425259, 14804887270297456, 29273851310515232,
    35405323751105105, 18375680075719645, 40298841116592240, 18412912981918629, 13440220327914385, 18375680075719645,
    17561235728877581, 18412912981918629, 22377447001893833, 12703254733826280, 35405323751105105, 18375680075719645,
    13440220327914385, 12703254733826280, 13440220327914385, 17385078773721895, 17561235728877581, 31273797535754285,
    34074149250211215, 38283467978287005, 38283382100527962, 34077325606718864, 23826966301791860, 30450787466195458,
    18375680075719645, 35579108021289978, 18412912981918629, 13440220327914385, 18375680075719645, 17561235728877581,
    18412912981918629, 22377447001893833, 12703254733826280, 30450787466195458, 18375680075719645, 13440220327914385,
    12703254733826280, 13440220327914385, 17385078773721895, 17561235728877581, 25826877227219643, 32646042356762138,
    36847438421734297, 36847360891569808, 32648895840025130, 31841625534742786
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
noncomputable def negativeCeiling : ℝ := 653015361 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 149620587715773863294926848, coefficient := (-149620587715773863294926848) }, { argument := 1035331627704341016650711040, coefficient := (-1035331627704341016650711040) }, { argument := 805257932658931901839441920, coefficient := (-805257932658931901839441920) }, { argument := 920294780181636459245076480, coefficient := (-920294780181636459245076480) }, { argument := 1081346366713422839612964864, coefficient := (-1081346366713422839612964864) }, { argument := 12769090075020205872025436160, coefficient := (-12769090075020205872025436160) }, { argument := 28713197141667057528446386176, coefficient := (-28713197141667057528446386176) }, { argument := 805257932658931901839441920, coefficient := (-805257932658931901839441920) }, { argument := 12769090075020205872025436160, coefficient := (-12769090075020205872025436160) }, { argument := 920294780181636459245076480, coefficient := (-920294780181636459245076480) }, { argument := 897287410677095547763949568, coefficient := (-897287410677095547763949568) }, { argument := 897287410677095547763949568, coefficient := (-897287410677095547763949568) }, { argument := 897287410677095547763949568, coefficient := (-897287410677095547763949568) }, { argument := 28713197141667057528446386176, coefficient := (-28713197141667057528446386176) }, { argument := 897287410677095547763949568, coefficient := (-897287410677095547763949568) }, { argument := 1035331627704341016650711040, coefficient := (-1035331627704341016650711040) }, { argument := 1081346366713422839612964864, coefficient := (-1081346366713422839612964864) }, { argument := 2993415921275873719050305536, coefficient := (-2993415921275873719050305536) }, { argument := 209857350961950780521877340160, coefficient := (-209857350961950780521877340160) }, { argument := 51397330105188507533986234368, coefficient := (-51397330105188507533986234368) }, { argument := 1559407815235081996568342036480, coefficient := (-1559407815235081996568342036480) }, { argument := 52741051153690167861672148992, coefficient := (-52741051153690167861672148992) }, { argument := 1679651310627075409607393280, coefficient := (-1679651310627075409607393280) }, { argument := 51397330105188507533986234368, coefficient := (-51397330105188507533986234368) }, { argument := 29225932804911112127168643072, coefficient := (-29225932804911112127168643072) }, { argument := 52741051153690167861672148992, coefficient := (-52741051153690167861672148992) }, { argument := 823365072469392365789544185856, coefficient := (-823365072469392365789544185856) }, { argument := 32249305164039847864461950976, coefficient := (-32249305164039847864461950976) }, { argument := 209857350961950780521877340160, coefficient := (-209857350961950780521877340160) }, { argument := 51397330105188507533986234368, coefficient := (-51397330105188507533986234368) }, { argument := 1679651310627075409607393280, coefficient := (-1679651310627075409607393280) }, { argument := 32249305164039847864461950976, coefficient := (-32249305164039847864461950976) }, { argument := 1679651310627075409607393280, coefficient := (-1679651310627075409607393280) }, { argument := 51733260367313922615907713024, coefficient := (-51733260367313922615907713024) }, { argument := 29225932804911112127168643072, coefficient := (-29225932804911112127168643072) }, { argument := 2993304347297265391434203136, coefficient := (-2993304347297265391434203136) }, { argument := 20851665090675011248768155648, coefficient := (-20851665090675011248768155648) }, { argument := 771439611442655040240598646784, coefficient := (-771439611442655040240598646784) }, { argument := 771393692151711481809283842048, coefficient := (-771393692151711481809283842048) }, { argument := 20897624413359052639023661056, coefficient := (-20897624413359052639023661056) }, { argument := 137252824036367218558107648, coefficient := (-137252824036367218558107648) }, { argument := 13535993767985381795514286080, coefficient := (-13535993767985381795514286080) }, { argument := 1606166565787140860437069824, coefficient := (-1606166565787140860437069824) }, { argument := 118360957249618229359112355840, coefficient := (-118360957249618229359112355840) }, { argument := 1648157848552817745677254656, coefficient := (-1648157848552817745677254656) }, { argument := 52489103457096106550231040, coefficient := (-52489103457096106550231040) }, { argument := 1606166565787140860437069824, coefficient := (-1606166565787140860437069824) }, { argument := 913310400153472253974020096, coefficient := (-913310400153472253974020096) }, { argument := 1648157848552817745677254656, coefficient := (-1648157848552817745677254656) }, { argument := 25730158514668511430923255808, coefficient := (-25730158514668511430923255808) }, { argument := 1007790786376245245764435968, coefficient := (-1007790786376245245764435968) }, { argument := 13535993767985381795514286080, coefficient := (-13535993767985381795514286080) }, { argument := 1606166565787140860437069824, coefficient := (-1606166565787140860437069824) }, { argument := 52489103457096106550231040, coefficient := (-52489103457096106550231040) }, { argument := 1007790786376245245764435968, coefficient := (-1007790786376245245764435968) }, { argument := 52489103457096106550231040, coefficient := (-52489103457096106550231040) }, { argument := 1616664386478560081747116032, coefficient := (-1616664386478560081747116032) }, { argument := 913310400153472253974020096, coefficient := (-913310400153472253974020096) }, { argument := 137244350063308358232834048, coefficient := (-137244350063308358232834048) }, { argument := 15497716946997399766544941056, coefficient := (-15497716946997399766544941056) }, { argument := 570221986843755093509273550848, coefficient := (-570221986843755093509273550848) }, { argument := 570191344044060422924461408256, coefficient := (-570191344044060422924461408256) }, { argument := 15528399965205837056606994432, coefficient := (-15528399965205837056606994432) }, { argument := 70991134839318039348375453696, coefficient := (-70991134839318039348375453696) }] }

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

end TermShard9


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
