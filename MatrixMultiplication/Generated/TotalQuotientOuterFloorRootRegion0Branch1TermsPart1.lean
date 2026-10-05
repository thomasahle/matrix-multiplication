/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.SignedDyadicLogCanonical
import MatrixMultiplication.RationalDyadicLog

/-!
# Bounded directed term shards, root orientation 0, branch 1

Certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`.
Every proof below checks at most 64 signed terms.  The untrusted producer supplies integer
arrays and rational endpoints only; the direction of every logarithm bound is proved by the
committed generic checkers of `SignedDyadicLogCertificate` and `RationalDyadicLog`.
-/

namespace MatrixMultiplication.Generated.TotalQuotientOuterFloorRoot.Region0.Branch1

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace TermShard10

/-! Directed signed-log shard 10.  The untrusted producer supplies only integer arrays and
rational endpoints; the committed generic checker proves the direction of every logarithm. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (232587067827707782436111358361600)
def positiveArguments : Array ℕ := #[
    27616319, 39558511, 1787596865, 39558511, 45819884135695, 108226115,
    6717483, 39558511, 6717483, 27616319, 27616319, 28766028639,
    29471107741245, 4547064976708725, 4548185185976325, 58558651795785, 1177288510569255, 2102510665668643,
    1177534403007635, 158044251, 572914153, 39558511, 26837703, 97287309,
    6717483, 432385215, 1567406645, 108226115, 110332779, 399958937,
    27616319, 158044251, 572914153, 39558511, 7141810965, 25889233895,
    1787596865, 158044251, 572914153, 39558511, 1518361818963, 117088464735471,
    58558651795785, 3016904831449, 11452361362863, 163671596327989, 45819884135695, 432385215,
    1567406645, 108226115, 26837703, 97287309, 6717483, 158044251,
    572914153, 39558511, 26837703, 97287309, 6717483, 110332779,
    399958937, 27616319, 110332779, 399958937
  ]
def positiveCoefficients : Array ℕ := #[
    509431168850922490774421504, 364862864177012054203301888, 8243835468905130847329320960, 364862864177012054203301888, 25794301639959412897312931840, 499104861374214602447912960,
    61957844860247329959051264, 364862864177012054203301888, 61957844860247329959051264, 509431168850922490774421504, 509431168850922490774421504, 1036405406876235329597079552,
    33181517460416680512328826880, 1279885008420927936453515673600, 1280200319298436707468391219200, 32965590300851994053490769920, 331377256094203941229984481280, 1183608281305974263997966319616,
    331446468662570278145553858560, 364425231314764359587069952, 1321050094574634666511302656, 364862864177012054203301888, 61883529845903381816672256, 224329261342862490539655168,
    61957844860247329959051264, 498506212647555020189859840, 1807096827484170062680555520, 499104861374214602447912960, 508820134288538917159305216, 1844485037707980477770498048,
    509431168850922490774421504, 364425231314764359587069952, 1321050094574634666511302656, 364862864177012054203301888, 8233947443385477747273891840, 29848254495341981380137451520,
    8243835468905130847329320960, 364425231314764359587069952, 1321050094574634666511302656, 364862864177012054203301888, 854761715261919413409939456, 32957472884503166068746878976,
    32965590300851994053490769920, 849183217170372840122220544, 25788425183151036263798145024, 92138917529233187726654701568, 25794301639959412897312931840, 498506212647555020189859840,
    1807096827484170062680555520, 499104861374214602447912960, 61883529845903381816672256, 224329261342862490539655168, 61957844860247329959051264, 364425231314764359587069952,
    1321050094574634666511302656, 364862864177012054203301888, 61883529845903381816672256, 224329261342862490539655168, 61957844860247329959051264, 508820134288538917159305216,
    1844485037707980477770498048, 509431168850922490774421504, 508820134288538917159305216, 1844485037707980477770498048
  ]
def positiveScales : Array ℕ := #[
    24, 25, 30, 25, 45, 26,
    22, 25, 22, 24, 24, 34,
    44, 52, 52, 45, 50, 50,
    50, 27, 29, 25, 24, 26,
    22, 28, 30, 26, 26, 28,
    24, 27, 29, 25, 32, 34,
    30, 27, 29, 25, 40, 46,
    45, 41, 43, 47, 45, 28,
    30, 26, 24, 26, 22, 27,
    29, 25, 24, 26, 22, 26,
    28, 24, 26, 28
  ]
def negativeArguments : Array ℕ := #[]
def negativeCoefficients : Array ℕ := #[]
def negativeScales : Array ℕ := #[]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    24719017698704423, 25237484787645656, 30735374273695898, 25237484787645656, 45381039044053688, 26689473423093889,
    22679489334522015, 25237484787645656, 22679489334522015, 24719017698704423, 24719017698704423, 34743647009066278,
    44744366522107642, 52013857043382699, 52014212420163852, 45734947572155763, 50064389339066222, 50901034542073860,
    50064690633741662, 27235753315982309, 29093743736964501, 25237484787645656, 24677757862858781, 26535748283843561,
    22679489334522015, 28687741951430684, 30545732372416164, 26689473423093889, 26717286227041347, 28575276648030077,
    24719017698704423, 27235753315982309, 29093743736964501, 25237484787645656, 32733642802032934, 34591633223024566,
    30735374273695898, 27235753315982309, 29093743736964501, 25237484787645656, 40465652758271410, 46734592280523305,
    45734947572155763, 41456206325897920, 43380710331879895, 47217797305750059, 45381039044053688, 28687741951430684,
    30545732372416164, 26689473423093889, 24677757862858781, 26535748283843561, 22679489334522015, 27235753315982309,
    29093743736964501, 25237484787645656, 24677757862858781, 26535748283843561, 22679489334522015, 26717286227041347,
    28575276648030077, 24719017698704423, 26717286227041347, 28575276648030077
  ]
def negativeLogUpperNumerators : Array ℕ := #[]

abbrev PositiveTerm := Fin 64
abbrev NegativeTerm := Fin 0
def positiveArgument (term : PositiveTerm) : ℕ := positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ := positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ := positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ := negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ := negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ := negativeScales[term.val]?.getD 0
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

noncomputable def positiveExact : ℝ := Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ := Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 1463013133 / 500000000000
noncomputable def negativeCeiling : ℝ := 0 / 1

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
  norm_num [positiveRationalLower, positiveFloor, bits, positiveLogLower, logBoundDenominator,
    positiveLogLowerNumerator, positiveLogLowerNumerators, positiveCoefficient,
    positiveCoefficients, Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [negativeRationalUpper, negativeCeiling, bits, negativeLogUpper, logBoundDenominator,
    negativeLogUpperNumerator, negativeLogUpperNumerators, negativeCoefficient,
    negativeCoefficients, Fin.sum_univ_succ, mass]

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
def rawForm : Form := { constantNumerator := 0, terms := [
    { argument := 509431168850922490774421504, coefficient := (509431168850922490774421504) }, { argument := 364862864177012054203301888, coefficient := (364862864177012054203301888) },
    { argument := 8243835468905130847329320960, coefficient := (8243835468905130847329320960) }, { argument := 364862864177012054203301888, coefficient := (364862864177012054203301888) },
    { argument := 25794301639959412897312931840, coefficient := (25794301639959412897312931840) }, { argument := 499104861374214602447912960, coefficient := (499104861374214602447912960) },
    { argument := 61957844860247329959051264, coefficient := (61957844860247329959051264) }, { argument := 364862864177012054203301888, coefficient := (364862864177012054203301888) },
    { argument := 61957844860247329959051264, coefficient := (61957844860247329959051264) }, { argument := 509431168850922490774421504, coefficient := (509431168850922490774421504) },
    { argument := 509431168850922490774421504, coefficient := (509431168850922490774421504) }, { argument := 1036405406876235329597079552, coefficient := (1036405406876235329597079552) },
    { argument := 33181517460416680512328826880, coefficient := (33181517460416680512328826880) }, { argument := 1279885008420927936453515673600, coefficient := (1279885008420927936453515673600) },
    { argument := 1280200319298436707468391219200, coefficient := (1280200319298436707468391219200) }, { argument := 32965590300851994053490769920, coefficient := (32965590300851994053490769920) },
    { argument := 331377256094203941229984481280, coefficient := (331377256094203941229984481280) }, { argument := 1183608281305974263997966319616, coefficient := (1183608281305974263997966319616) },
    { argument := 331446468662570278145553858560, coefficient := (331446468662570278145553858560) }, { argument := 364425231314764359587069952, coefficient := (364425231314764359587069952) },
    { argument := 1321050094574634666511302656, coefficient := (1321050094574634666511302656) }, { argument := 364862864177012054203301888, coefficient := (364862864177012054203301888) },
    { argument := 61883529845903381816672256, coefficient := (61883529845903381816672256) }, { argument := 224329261342862490539655168, coefficient := (224329261342862490539655168) },
    { argument := 61957844860247329959051264, coefficient := (61957844860247329959051264) }, { argument := 498506212647555020189859840, coefficient := (498506212647555020189859840) },
    { argument := 1807096827484170062680555520, coefficient := (1807096827484170062680555520) }, { argument := 499104861374214602447912960, coefficient := (499104861374214602447912960) },
    { argument := 508820134288538917159305216, coefficient := (508820134288538917159305216) }, { argument := 1844485037707980477770498048, coefficient := (1844485037707980477770498048) },
    { argument := 509431168850922490774421504, coefficient := (509431168850922490774421504) }, { argument := 364425231314764359587069952, coefficient := (364425231314764359587069952) },
    { argument := 1321050094574634666511302656, coefficient := (1321050094574634666511302656) }, { argument := 364862864177012054203301888, coefficient := (364862864177012054203301888) },
    { argument := 8233947443385477747273891840, coefficient := (8233947443385477747273891840) }, { argument := 29848254495341981380137451520, coefficient := (29848254495341981380137451520) },
    { argument := 8243835468905130847329320960, coefficient := (8243835468905130847329320960) }, { argument := 364425231314764359587069952, coefficient := (364425231314764359587069952) },
    { argument := 1321050094574634666511302656, coefficient := (1321050094574634666511302656) }, { argument := 364862864177012054203301888, coefficient := (364862864177012054203301888) },
    { argument := 854761715261919413409939456, coefficient := (854761715261919413409939456) }, { argument := 32957472884503166068746878976, coefficient := (32957472884503166068746878976) },
    { argument := 32965590300851994053490769920, coefficient := (32965590300851994053490769920) }, { argument := 849183217170372840122220544, coefficient := (849183217170372840122220544) },
    { argument := 25788425183151036263798145024, coefficient := (25788425183151036263798145024) }, { argument := 92138917529233187726654701568, coefficient := (92138917529233187726654701568) },
    { argument := 25794301639959412897312931840, coefficient := (25794301639959412897312931840) }, { argument := 498506212647555020189859840, coefficient := (498506212647555020189859840) },
    { argument := 1807096827484170062680555520, coefficient := (1807096827484170062680555520) }, { argument := 499104861374214602447912960, coefficient := (499104861374214602447912960) },
    { argument := 61883529845903381816672256, coefficient := (61883529845903381816672256) }, { argument := 224329261342862490539655168, coefficient := (224329261342862490539655168) },
    { argument := 61957844860247329959051264, coefficient := (61957844860247329959051264) }, { argument := 364425231314764359587069952, coefficient := (364425231314764359587069952) },
    { argument := 1321050094574634666511302656, coefficient := (1321050094574634666511302656) }, { argument := 364862864177012054203301888, coefficient := (364862864177012054203301888) },
    { argument := 61883529845903381816672256, coefficient := (61883529845903381816672256) }, { argument := 224329261342862490539655168, coefficient := (224329261342862490539655168) },
    { argument := 61957844860247329959051264, coefficient := (61957844860247329959051264) }, { argument := 508820134288538917159305216, coefficient := (508820134288538917159305216) },
    { argument := 1844485037707980477770498048, coefficient := (1844485037707980477770498048) }, { argument := 509431168850922490774421504, coefficient := (509431168850922490774421504) },
    { argument := 508820134288538917159305216, coefficient := (508820134288538917159305216) }, { argument := 1844485037707980477770498048, coefficient := (1844485037707980477770498048) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form after bounded power-of-two normalization. -/
def form : Form := Form.normalizePowersOfTwo rawForm

theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by rfl

theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by decide +kernel

noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard10

namespace TermShard11

/-! Directed signed-log shard 11.  The untrusted producer supplies only integer arrays and
rational endpoints; the committed generic checker proves the direction of every logarithm. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-872066093474140537737537415806976)
def positiveArguments : Array ℕ := #[
    27616319, 460136189451, 1644860455941, 28766028639, 753204701115, 37184429831475,
    37179514063113, 754891528713, 76273940087, 3624444516245, 528545, 45562636772881,
    757105, 128565, 2071325, 528545, 757105, 34212575,
    757105, 904613877693, 2071325, 128565, 757105, 128565,
    528545, 528545, 18782598863, 76273940087, 11786392348379, 11789298837315,
    151566855171, 10739949091965, 530212945846725, 530142851884383, 10764001573983, 11786392348379,
    281665197174949, 603859129, 1776443244641599, 864987401, 146884653, 2366474965,
    603859129, 864987401, 39087638215, 864987401, 140597561694573, 2366474965,
    146884653, 864987401, 146884653, 603859129, 603859129, 1451689720165,
    3624444516245, 281665197174949, 140867453065185, 7204363382895, 528545, 603859129,
    604000395, 4185255, 753204701115
  ]
def positiveCoefficients : Array ℕ := #[
    509431168850922490774421504, 1036134585675601776211918848, 3703896468226175876745658368, 1036405406876235329597079552, 848033102818804953262325760, 41865946083253791343666790400,
    41860411420112955625294528512, 849932301854252720468262912, 85876822038473184313868288, 2040380871598252454513213440, 77999474771510519671029760, 25649484249045516248649039872,
    55864488687703480304926720, 9486422607345874014044160, 76418404336952874002022400, 77999474771510519671029760, 55864488687703480304926720, 1262221230255187125757542400,
    55864488687703480304926720, 2037009361246187121870372864, 76418404336952874002022400, 9486422607345874014044160, 55864488687703480304926720, 9486422607345874014044160,
    77999474771510519671029760, 77999474771510519671029760, 84589305240456301849346048, 85876822038473184313868288, 3317574511762633104633626624, 3318392615668203483970928640,
    85324554058729191848804352, 3023026920534479429739479040, 149241676583895230297250201600, 149221946887477458248556085248, 3029797092350329451968462848, 3317574511762633104633626624,
    79281704815021099939784556544, 2784808702309040409454575616, 1000048641826592515181288357888, 1994525151653772185149898752, 338692950280829238987718656, 2728359877262235536289955840,
    2784808702309040409454575616, 1994525151653772185149898752, 45064978662365890409754787840, 1994525151653772185149898752, 79149390807109910617732939776, 2728359877262235536289955840,
    338692950280829238987718656, 1994525151653772185149898752, 338692950280829238987718656, 2784808702309040409454575616, 2784808702309040409454575616, 3268914641396336806508625920,
    2040380871598252454513213440, 79281704815021099939784556544, 79301326141624750072104222720, 2027848015415472999754629120, 77999474771510519671029760, 2784808702309040409454575616,
    2785460176746119572834222080, 77204327868213269448622080, 848033102818804953262325760
  ]
def positiveScales : Array ℕ := #[
    24, 38, 40, 34, 39, 45,
    45, 39, 36, 41, 19, 45,
    19, 16, 20, 19, 19, 25,
    19, 39, 20, 16, 19, 16,
    19, 19, 34, 36, 43, 43,
    37, 43, 48, 48, 43, 43,
    48, 29, 50, 29, 27, 31,
    29, 29, 35, 29, 46, 31,
    27, 29, 27, 29, 29, 40,
    41, 48, 47, 42, 19, 29,
    29, 21, 39
  ]
def negativeArguments : Array ℕ := #[
    31
  ]
def negativeCoefficients : Array ℕ := #[
    9824292151768777861599449841664
  ]
def negativeScales : Array ℕ := #[
    4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    24719017698704423, 38743269971801236, 40581102334729462, 34743647009066278, 39454251048299065, 45079763884245170,
    45079573147867379, 39457478400476200, 36150471175931198, 41720897042715818, 19011666781452684, 45372916473757418,
    19530133870386888, 16972138416335880, 20982122504743718, 19011666781452684, 19530133870386888, 25028023356447276,
    19530133870386888, 39718511172296141, 20982122504743718, 16972138416335880, 19530133870386888, 16972138416335880,
    19011666781452684, 19011666781452684, 34128677644845004, 36150471175931198, 43422187430430888, 43422543150834806,
    37141163341409269, 43288052388409901, 48913565224012513, 48913374487635874, 43291279740587037, 43422187430430888,
    48000974642349008, 29169636789449046, 50657913020234585, 29688103878379906, 27130108425262409, 31140092513835031,
    29169636789449046, 29688103878379906, 35185993364443639, 29688103878379906, 46998564901765030, 31140092513835031,
    27130108425262409, 29688103878379906, 27130108425262409, 29169636789449046, 29169636789449046, 40400870267591951,
    41720897042715818, 48000974642349008, 47001331648903372, 42712008090219590, 19011666781452684, 29169636789449046,
    29169974252133283, 21996884094182361, 39454251048299065
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    4954196321574415
  ]

abbrev PositiveTerm := Fin 63
abbrev NegativeTerm := Fin 1
def positiveArgument (term : PositiveTerm) : ℕ := positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ := positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ := positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ := negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ := negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ := negativeScales[term.val]?.getD 0
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

noncomputable def positiveExact : ℝ := Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ := Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 1075244293 / 1000000000000
noncomputable def negativeCeiling : ℝ := 292930767 / 500000000000

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
  norm_num [positiveRationalLower, positiveFloor, bits, positiveLogLower, logBoundDenominator,
    positiveLogLowerNumerator, positiveLogLowerNumerators, positiveCoefficient,
    positiveCoefficients, Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [negativeRationalUpper, negativeCeiling, bits, negativeLogUpper, logBoundDenominator,
    negativeLogUpperNumerator, negativeLogUpperNumerators, negativeCoefficient,
    negativeCoefficients, Fin.sum_univ_succ, mass]

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
def rawForm : Form := { constantNumerator := 0, terms := [
    { argument := 509431168850922490774421504, coefficient := (509431168850922490774421504) }, { argument := 1036134585675601776211918848, coefficient := (1036134585675601776211918848) },
    { argument := 3703896468226175876745658368, coefficient := (3703896468226175876745658368) }, { argument := 1036405406876235329597079552, coefficient := (1036405406876235329597079552) },
    { argument := 9824292151768777861599449841664, coefficient := (-9824292151768777861599449841664) }, { argument := 848033102818804953262325760, coefficient := (848033102818804953262325760) },
    { argument := 41865946083253791343666790400, coefficient := (41865946083253791343666790400) }, { argument := 41860411420112955625294528512, coefficient := (41860411420112955625294528512) },
    { argument := 849932301854252720468262912, coefficient := (849932301854252720468262912) }, { argument := 85876822038473184313868288, coefficient := (85876822038473184313868288) },
    { argument := 2040380871598252454513213440, coefficient := (2040380871598252454513213440) }, { argument := 77999474771510519671029760, coefficient := (77999474771510519671029760) },
    { argument := 25649484249045516248649039872, coefficient := (25649484249045516248649039872) }, { argument := 55864488687703480304926720, coefficient := (55864488687703480304926720) },
    { argument := 9486422607345874014044160, coefficient := (9486422607345874014044160) }, { argument := 76418404336952874002022400, coefficient := (76418404336952874002022400) },
    { argument := 77999474771510519671029760, coefficient := (77999474771510519671029760) }, { argument := 55864488687703480304926720, coefficient := (55864488687703480304926720) },
    { argument := 1262221230255187125757542400, coefficient := (1262221230255187125757542400) }, { argument := 55864488687703480304926720, coefficient := (55864488687703480304926720) },
    { argument := 2037009361246187121870372864, coefficient := (2037009361246187121870372864) }, { argument := 76418404336952874002022400, coefficient := (76418404336952874002022400) },
    { argument := 9486422607345874014044160, coefficient := (9486422607345874014044160) }, { argument := 55864488687703480304926720, coefficient := (55864488687703480304926720) },
    { argument := 9486422607345874014044160, coefficient := (9486422607345874014044160) }, { argument := 77999474771510519671029760, coefficient := (77999474771510519671029760) },
    { argument := 77999474771510519671029760, coefficient := (77999474771510519671029760) }, { argument := 84589305240456301849346048, coefficient := (84589305240456301849346048) },
    { argument := 85876822038473184313868288, coefficient := (85876822038473184313868288) }, { argument := 3317574511762633104633626624, coefficient := (3317574511762633104633626624) },
    { argument := 3318392615668203483970928640, coefficient := (3318392615668203483970928640) }, { argument := 85324554058729191848804352, coefficient := (85324554058729191848804352) },
    { argument := 3023026920534479429739479040, coefficient := (3023026920534479429739479040) }, { argument := 149241676583895230297250201600, coefficient := (149241676583895230297250201600) },
    { argument := 149221946887477458248556085248, coefficient := (149221946887477458248556085248) }, { argument := 3029797092350329451968462848, coefficient := (3029797092350329451968462848) },
    { argument := 3317574511762633104633626624, coefficient := (3317574511762633104633626624) }, { argument := 79281704815021099939784556544, coefficient := (79281704815021099939784556544) },
    { argument := 2784808702309040409454575616, coefficient := (2784808702309040409454575616) }, { argument := 1000048641826592515181288357888, coefficient := (1000048641826592515181288357888) },
    { argument := 1994525151653772185149898752, coefficient := (1994525151653772185149898752) }, { argument := 338692950280829238987718656, coefficient := (338692950280829238987718656) },
    { argument := 2728359877262235536289955840, coefficient := (2728359877262235536289955840) }, { argument := 2784808702309040409454575616, coefficient := (2784808702309040409454575616) },
    { argument := 1994525151653772185149898752, coefficient := (1994525151653772185149898752) }, { argument := 45064978662365890409754787840, coefficient := (45064978662365890409754787840) },
    { argument := 1994525151653772185149898752, coefficient := (1994525151653772185149898752) }, { argument := 79149390807109910617732939776, coefficient := (79149390807109910617732939776) },
    { argument := 2728359877262235536289955840, coefficient := (2728359877262235536289955840) }, { argument := 338692950280829238987718656, coefficient := (338692950280829238987718656) },
    { argument := 1994525151653772185149898752, coefficient := (1994525151653772185149898752) }, { argument := 338692950280829238987718656, coefficient := (338692950280829238987718656) },
    { argument := 2784808702309040409454575616, coefficient := (2784808702309040409454575616) }, { argument := 2784808702309040409454575616, coefficient := (2784808702309040409454575616) },
    { argument := 3268914641396336806508625920, coefficient := (3268914641396336806508625920) }, { argument := 2040380871598252454513213440, coefficient := (2040380871598252454513213440) },
    { argument := 79281704815021099939784556544, coefficient := (79281704815021099939784556544) }, { argument := 79301326141624750072104222720, coefficient := (79301326141624750072104222720) },
    { argument := 2027848015415472999754629120, coefficient := (2027848015415472999754629120) }, { argument := 77999474771510519671029760, coefficient := (77999474771510519671029760) },
    { argument := 2784808702309040409454575616, coefficient := (2784808702309040409454575616) }, { argument := 2785460176746119572834222080, coefficient := (2785460176746119572834222080) },
    { argument := 77204327868213269448622080, coefficient := (77204327868213269448622080) }, { argument := 848033102818804953262325760, coefficient := (848033102818804953262325760) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form after bounded power-of-two normalization. -/
def form : Form := Form.normalizePowersOfTwo rawForm

theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by rfl

theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by decide +kernel

noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard11

namespace TermShard12

/-! Directed signed-log shard 12.  The untrusted producer supplies only integer arrays and
rational endpoints; the committed generic checker proves the direction of every logarithm. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (183821877423088479545894484574208)
def positiveArguments : Array ℕ := #[
    10739949091965, 3012955710615, 3012955710615, 148744478148975, 148724814182013, 3019703327613,
    11789298837315, 140867453065185, 604000395, 3553767643816545, 865189755, 146919015,
    2367028575, 604000395, 865189755, 39096782325, 865189755, 140632357646445,
    2367028575, 146919015, 865189755, 146919015, 604000395, 604000395,
    181505972055, 45562636772881, 1776443244641599, 3553767643816545, 90581083330303, 757105,
    864987401, 865189755, 5995095, 37184429831475, 530212945846725, 148744478148975,
    128565, 146884653, 146919015, 1018035, 2071325, 2366474965,
    2367028575, 16401675, 528545, 603859129, 604000395, 4185255,
    757105, 864987401, 865189755, 5995095, 34212575, 39087638215,
    39096782325, 270910425, 757105, 864987401, 865189755, 5995095,
    151566855171, 7204363382895, 4185255, 90581083330303
  ]
def positiveCoefficients : Array ℕ := #[
    3023026920534479429739479040, 848071638475595123722813440, 848071638475595123722813440, 41867848522821418413037977600, 41862313608178750354020630528, 849970923812959600276144128,
    3318392615668203483970928640, 79301326141624750072104222720, 2785460176746119572834222080, 1000296664778344850962010603520, 1994991748210058612975861760, 338772183658311839939297280,
    2728998146136400932844339200, 2785460176746119572834222080, 1994991748210058612975861760, 45075521103425380925256499200, 1994991748210058612975861760, 79168979186595503231824035840,
    2728998146136400932844339200, 338772183658311839939297280, 1994991748210058612975861760, 338772183658311839939297280, 2785460176746119572834222080, 2785460176746119572834222080,
    3269720912449670640429957120, 25649484249045516248649039872, 1000048641826592515181288357888, 1000296664778344850962010603520, 25496308320823027352907808768, 55864488687703480304926720,
    1994525151653772185149898752, 1994991748210058612975861760, 55294991581287882172661760, 41865946083253791343666790400, 149241676583895230297250201600, 41867848522821418413037977600,
    9486422607345874014044160, 338692950280829238987718656, 338772183658311839939297280, 9389715551539451689697280, 76418404336952874002022400, 2728359877262235536289955840,
    2728998146136400932844339200, 75639375276290027500339200, 77999474771510519671029760, 2784808702309040409454575616, 2785460176746119572834222080, 77204327868213269448622080,
    55864488687703480304926720, 1994525151653772185149898752, 1994991748210058612975861760, 55294991581287882172661760, 1262221230255187125757542400, 45064978662365890409754787840,
    45075521103425380925256499200, 1249353819218721488712499200, 55864488687703480304926720, 1994525151653772185149898752, 1994991748210058612975861760, 55294991581287882172661760,
    85324554058729191848804352, 2027848015415472999754629120, 77204327868213269448622080, 25496308320823027352907808768
  ]
def positiveScales : Array ℕ := #[
    43, 41, 41, 47, 47, 41,
    43, 47, 29, 51, 29, 27,
    31, 29, 29, 35, 29, 46,
    31, 27, 29, 27, 29, 29,
    37, 45, 50, 51, 46, 19,
    29, 29, 22, 45, 48, 47,
    16, 27, 27, 19, 20, 31,
    31, 23, 19, 29, 29, 21,
    19, 29, 29, 22, 25, 35,
    35, 28, 19, 29, 29, 22,
    37, 42, 21, 46
  ]
def negativeArguments : Array ℕ := #[]
def negativeCoefficients : Array ℕ := #[]
def negativeScales : Array ℕ := #[]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    43288052388409901, 41454316604628936, 41454316604628936, 47079829440575041, 47079638704197250, 41457543956806071,
    43422543150834806, 47001331648903372, 29169974252133283, 51658270779950527, 29688441341064116, 27130445887946646,
    31140429976519268, 29169974252133283, 29688441341064116, 35186330827127876, 29688441341064116, 46998921904650341,
    31140429976519268, 27130445887946646, 29688441341064116, 27130445887946646, 29169974252133283, 29169974252133283,
    37401226061471752, 45372916473757418, 50657913020234585, 51658270779950527, 46364275027349763, 19530133870386888,
    29688103878379906, 29688441341064116, 22515351184505423, 45079763884245170, 48913565224012513, 47079829440575041,
    16972138416335880, 27130108425262409, 27130445887946646, 19957355730656501, 20982122504743718, 31140092513835031,
    31140429976519268, 23967339819097728, 19011666781452684, 29169636789449046, 29169974252133283, 21996884094182361,
    19530133870386888, 29688103878379906, 29688441341064116, 22515351184505423, 25028023356447276, 35185993364443639,
    35186330827127876, 28013240670565795, 19530133870386888, 29688103878379906, 29688441341064116, 22515351184505423,
    37141163341409269, 42712008090219590, 21996884094182361, 46364275027349763
  ]
def negativeLogUpperNumerators : Array ℕ := #[]

abbrev PositiveTerm := Fin 64
abbrev NegativeTerm := Fin 0
def positiveArgument (term : PositiveTerm) : ℕ := positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ := positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ := positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ := negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ := negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ := negativeScales[term.val]?.getD 0
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

noncomputable def positiveExact : ℝ := Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ := Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 450143383 / 200000000000
noncomputable def negativeCeiling : ℝ := 0 / 1

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
  norm_num [positiveRationalLower, positiveFloor, bits, positiveLogLower, logBoundDenominator,
    positiveLogLowerNumerator, positiveLogLowerNumerators, positiveCoefficient,
    positiveCoefficients, Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [negativeRationalUpper, negativeCeiling, bits, negativeLogUpper, logBoundDenominator,
    negativeLogUpperNumerator, negativeLogUpperNumerators, negativeCoefficient,
    negativeCoefficients, Fin.sum_univ_succ, mass]

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
def rawForm : Form := { constantNumerator := 0, terms := [
    { argument := 3023026920534479429739479040, coefficient := (3023026920534479429739479040) }, { argument := 848071638475595123722813440, coefficient := (848071638475595123722813440) },
    { argument := 848071638475595123722813440, coefficient := (848071638475595123722813440) }, { argument := 41867848522821418413037977600, coefficient := (41867848522821418413037977600) },
    { argument := 41862313608178750354020630528, coefficient := (41862313608178750354020630528) }, { argument := 849970923812959600276144128, coefficient := (849970923812959600276144128) },
    { argument := 3318392615668203483970928640, coefficient := (3318392615668203483970928640) }, { argument := 79301326141624750072104222720, coefficient := (79301326141624750072104222720) },
    { argument := 2785460176746119572834222080, coefficient := (2785460176746119572834222080) }, { argument := 1000296664778344850962010603520, coefficient := (1000296664778344850962010603520) },
    { argument := 1994991748210058612975861760, coefficient := (1994991748210058612975861760) }, { argument := 338772183658311839939297280, coefficient := (338772183658311839939297280) },
    { argument := 2728998146136400932844339200, coefficient := (2728998146136400932844339200) }, { argument := 2785460176746119572834222080, coefficient := (2785460176746119572834222080) },
    { argument := 1994991748210058612975861760, coefficient := (1994991748210058612975861760) }, { argument := 45075521103425380925256499200, coefficient := (45075521103425380925256499200) },
    { argument := 1994991748210058612975861760, coefficient := (1994991748210058612975861760) }, { argument := 79168979186595503231824035840, coefficient := (79168979186595503231824035840) },
    { argument := 2728998146136400932844339200, coefficient := (2728998146136400932844339200) }, { argument := 338772183658311839939297280, coefficient := (338772183658311839939297280) },
    { argument := 1994991748210058612975861760, coefficient := (1994991748210058612975861760) }, { argument := 338772183658311839939297280, coefficient := (338772183658311839939297280) },
    { argument := 2785460176746119572834222080, coefficient := (2785460176746119572834222080) }, { argument := 2785460176746119572834222080, coefficient := (2785460176746119572834222080) },
    { argument := 3269720912449670640429957120, coefficient := (3269720912449670640429957120) }, { argument := 25649484249045516248649039872, coefficient := (25649484249045516248649039872) },
    { argument := 1000048641826592515181288357888, coefficient := (1000048641826592515181288357888) }, { argument := 1000296664778344850962010603520, coefficient := (1000296664778344850962010603520) },
    { argument := 25496308320823027352907808768, coefficient := (25496308320823027352907808768) }, { argument := 55864488687703480304926720, coefficient := (55864488687703480304926720) },
    { argument := 1994525151653772185149898752, coefficient := (1994525151653772185149898752) }, { argument := 1994991748210058612975861760, coefficient := (1994991748210058612975861760) },
    { argument := 55294991581287882172661760, coefficient := (55294991581287882172661760) }, { argument := 41865946083253791343666790400, coefficient := (41865946083253791343666790400) },
    { argument := 149241676583895230297250201600, coefficient := (149241676583895230297250201600) }, { argument := 41867848522821418413037977600, coefficient := (41867848522821418413037977600) },
    { argument := 9486422607345874014044160, coefficient := (9486422607345874014044160) }, { argument := 338692950280829238987718656, coefficient := (338692950280829238987718656) },
    { argument := 338772183658311839939297280, coefficient := (338772183658311839939297280) }, { argument := 9389715551539451689697280, coefficient := (9389715551539451689697280) },
    { argument := 76418404336952874002022400, coefficient := (76418404336952874002022400) }, { argument := 2728359877262235536289955840, coefficient := (2728359877262235536289955840) },
    { argument := 2728998146136400932844339200, coefficient := (2728998146136400932844339200) }, { argument := 75639375276290027500339200, coefficient := (75639375276290027500339200) },
    { argument := 77999474771510519671029760, coefficient := (77999474771510519671029760) }, { argument := 2784808702309040409454575616, coefficient := (2784808702309040409454575616) },
    { argument := 2785460176746119572834222080, coefficient := (2785460176746119572834222080) }, { argument := 77204327868213269448622080, coefficient := (77204327868213269448622080) },
    { argument := 55864488687703480304926720, coefficient := (55864488687703480304926720) }, { argument := 1994525151653772185149898752, coefficient := (1994525151653772185149898752) },
    { argument := 1994991748210058612975861760, coefficient := (1994991748210058612975861760) }, { argument := 55294991581287882172661760, coefficient := (55294991581287882172661760) },
    { argument := 1262221230255187125757542400, coefficient := (1262221230255187125757542400) }, { argument := 45064978662365890409754787840, coefficient := (45064978662365890409754787840) },
    { argument := 45075521103425380925256499200, coefficient := (45075521103425380925256499200) }, { argument := 1249353819218721488712499200, coefficient := (1249353819218721488712499200) },
    { argument := 55864488687703480304926720, coefficient := (55864488687703480304926720) }, { argument := 1994525151653772185149898752, coefficient := (1994525151653772185149898752) },
    { argument := 1994991748210058612975861760, coefficient := (1994991748210058612975861760) }, { argument := 55294991581287882172661760, coefficient := (55294991581287882172661760) },
    { argument := 85324554058729191848804352, coefficient := (85324554058729191848804352) }, { argument := 2027848015415472999754629120, coefficient := (2027848015415472999754629120) },
    { argument := 77204327868213269448622080, coefficient := (77204327868213269448622080) }, { argument := 25496308320823027352907808768, coefficient := (25496308320823027352907808768) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form after bounded power-of-two normalization. -/
def form : Form := Form.normalizePowersOfTwo rawForm

theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by rfl

theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by decide +kernel

noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard12

namespace TermShard13

/-! Directed signed-log shard 13.  The untrusted producer supplies only integer arrays and
rational endpoints; the committed generic checker proves the direction of every logarithm. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-568225936065278887947517953048576)
def positiveArguments : Array ℕ := #[
    5995095, 1018035, 16401675, 4185255, 5995095, 270910425,
    5995095, 1798113242009, 16401675, 1018035, 5995095, 1018035,
    4185255, 4185255, 37324234309, 904613877693, 140597561694573, 140632357646445,
    1798113242009, 37179514063113, 530142851884383, 148724814182013, 2071325, 2366474965,
    2367028575, 16401675, 128565, 146884653, 146919015, 1018035,
    757105, 864987401, 865189755, 5995095, 128565, 146884653,
    146919015, 1018035, 528545, 603859129, 604000395, 4185255,
    528545, 603859129, 604000395, 4185255, 18782598863, 1451689720165,
    181505972055, 37324234309, 754891528713, 10764001573983, 3019703327613, 4758404925,
    234914325125, 234883269535, 4769061535, 28253805075, 360805826259, 9425534502189,
    360179085501, 874096653, 5436445815285
  ]
def positiveCoefficients : Array ℕ := #[
    55294991581287882172661760, 9389715551539451689697280, 75639375276290027500339200, 77204327868213269448622080, 55294991581287882172661760, 1249353819218721488712499200,
    55294991581287882172661760, 2024495531670421723588591616, 75639375276290027500339200, 9389715551539451689697280, 55294991581287882172661760, 9389715551539451689697280,
    77204327868213269448622080, 77204327868213269448622080, 84046703862950741128773632, 2037009361246187121870372864, 79149390807109910617732939776, 79168979186595503231824035840,
    2024495531670421723588591616, 41860411420112955625294528512, 149221946887477458248556085248, 41862313608178750354020630528, 76418404336952874002022400, 2728359877262235536289955840,
    2728998146136400932844339200, 75639375276290027500339200, 9486422607345874014044160, 338692950280829238987718656, 338772183658311839939297280, 9389715551539451689697280,
    55864488687703480304926720, 1994525151653772185149898752, 1994991748210058612975861760, 55294991581287882172661760, 9486422607345874014044160, 338692950280829238987718656,
    338772183658311839939297280, 9389715551539451689697280, 77999474771510519671029760, 2784808702309040409454575616, 2785460176746119572834222080, 77204327868213269448622080,
    77999474771510519671029760, 2784808702309040409454575616, 2785460176746119572834222080, 77204327868213269448622080, 84589305240456301849346048, 3268914641396336806508625920,
    3269720912449670640429957120, 84046703862950741128773632, 849932301854252720468262912, 3029797092350329451968462848, 849970923812959600276144128, 42859901294215865932185600,
    2115920134193883092353024000, 2115640410306779550549278720, 42955887503865931334942720, 7952739125473039299379200, 203115623086642040099831808, 2653052104489133369651625984,
    202762799406118702323597312, 7873162721473195489099776, 1530223459246088645467176960
  ]
def positiveScales : Array ℕ := #[
    22, 19, 23, 21, 22, 28,
    22, 40, 23, 19, 22, 19,
    21, 21, 35, 39, 46, 46,
    40, 45, 48, 47, 20, 31,
    31, 23, 16, 27, 27, 19,
    19, 29, 29, 22, 16, 27,
    27, 19, 19, 29, 29, 21,
    19, 29, 29, 21, 34, 40,
    37, 35, 39, 43, 41, 32,
    37, 37, 32, 34, 38, 43,
    38, 29, 42
  ]
def negativeArguments : Array ℕ := #[
    19
  ]
def negativeCoefficients : Array ℕ := #[
    6021340351084089657109340225536
  ]
def negativeScales : Array ℕ := #[
    4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    22515351184505423, 19957355730656501, 23967339819097728, 21996884094182361, 22515351184505423, 28013240670565795,
    22515351184505423, 40709621020752147, 23967339819097728, 19957355730656501, 22515351184505423, 19957355730656501,
    21996884094182361, 21996884094182361, 35119393613253820, 39718511172296141, 46998564901765030, 46998921904650341,
    40709621020752147, 45079573147867379, 48913374487635874, 47079638704197250, 20982122504743718, 31140092513835031,
    31140429976519268, 23967339819097728, 16972138416335880, 27130108425262409, 27130445887946646, 19957355730656501,
    19530133870386888, 29688103878379906, 29688441341064116, 22515351184505423, 16972138416335880, 27130108425262409,
    27130445887946646, 19957355730656501, 19011666781452684, 29169636789449046, 29169974252133283, 21996884094182361,
    19011666781452684, 29169636789449046, 29169974252133283, 21996884094182361, 34128677644845004, 40400870267591951,
    37401226061471752, 35119393613253820, 39457478400476200, 43291279740587037, 41457543956806071, 32147830899694803,
    37773343735617877, 37773152999240179, 32151058251871938, 34717726124117262, 38392431679048015, 43099711571543454,
    38389923454544299, 29703217573252635, 42305800907691165
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    4247927513443586
  ]

abbrev PositiveTerm := Fin 63
abbrev NegativeTerm := Fin 1
def positiveArgument (term : PositiveTerm) : ℕ := positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ := positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ := positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ := negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ := negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ := negativeScales[term.val]?.getD 0
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

noncomputable def positiveExact : ℝ := Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ := Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 122636061 / 500000000000
noncomputable def negativeCeiling : ℝ := 601341 / 1953125000

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
  norm_num [positiveRationalLower, positiveFloor, bits, positiveLogLower, logBoundDenominator,
    positiveLogLowerNumerator, positiveLogLowerNumerators, positiveCoefficient,
    positiveCoefficients, Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [negativeRationalUpper, negativeCeiling, bits, negativeLogUpper, logBoundDenominator,
    negativeLogUpperNumerator, negativeLogUpperNumerators, negativeCoefficient,
    negativeCoefficients, Fin.sum_univ_succ, mass]

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
def rawForm : Form := { constantNumerator := 0, terms := [
    { argument := 55294991581287882172661760, coefficient := (55294991581287882172661760) }, { argument := 9389715551539451689697280, coefficient := (9389715551539451689697280) },
    { argument := 75639375276290027500339200, coefficient := (75639375276290027500339200) }, { argument := 77204327868213269448622080, coefficient := (77204327868213269448622080) },
    { argument := 55294991581287882172661760, coefficient := (55294991581287882172661760) }, { argument := 1249353819218721488712499200, coefficient := (1249353819218721488712499200) },
    { argument := 55294991581287882172661760, coefficient := (55294991581287882172661760) }, { argument := 2024495531670421723588591616, coefficient := (2024495531670421723588591616) },
    { argument := 75639375276290027500339200, coefficient := (75639375276290027500339200) }, { argument := 9389715551539451689697280, coefficient := (9389715551539451689697280) },
    { argument := 55294991581287882172661760, coefficient := (55294991581287882172661760) }, { argument := 9389715551539451689697280, coefficient := (9389715551539451689697280) },
    { argument := 77204327868213269448622080, coefficient := (77204327868213269448622080) }, { argument := 77204327868213269448622080, coefficient := (77204327868213269448622080) },
    { argument := 84046703862950741128773632, coefficient := (84046703862950741128773632) }, { argument := 2037009361246187121870372864, coefficient := (2037009361246187121870372864) },
    { argument := 79149390807109910617732939776, coefficient := (79149390807109910617732939776) }, { argument := 79168979186595503231824035840, coefficient := (79168979186595503231824035840) },
    { argument := 2024495531670421723588591616, coefficient := (2024495531670421723588591616) }, { argument := 41860411420112955625294528512, coefficient := (41860411420112955625294528512) },
    { argument := 149221946887477458248556085248, coefficient := (149221946887477458248556085248) }, { argument := 41862313608178750354020630528, coefficient := (41862313608178750354020630528) },
    { argument := 76418404336952874002022400, coefficient := (76418404336952874002022400) }, { argument := 2728359877262235536289955840, coefficient := (2728359877262235536289955840) },
    { argument := 2728998146136400932844339200, coefficient := (2728998146136400932844339200) }, { argument := 75639375276290027500339200, coefficient := (75639375276290027500339200) },
    { argument := 9486422607345874014044160, coefficient := (9486422607345874014044160) }, { argument := 338692950280829238987718656, coefficient := (338692950280829238987718656) },
    { argument := 338772183658311839939297280, coefficient := (338772183658311839939297280) }, { argument := 9389715551539451689697280, coefficient := (9389715551539451689697280) },
    { argument := 55864488687703480304926720, coefficient := (55864488687703480304926720) }, { argument := 1994525151653772185149898752, coefficient := (1994525151653772185149898752) },
    { argument := 1994991748210058612975861760, coefficient := (1994991748210058612975861760) }, { argument := 55294991581287882172661760, coefficient := (55294991581287882172661760) },
    { argument := 9486422607345874014044160, coefficient := (9486422607345874014044160) }, { argument := 338692950280829238987718656, coefficient := (338692950280829238987718656) },
    { argument := 338772183658311839939297280, coefficient := (338772183658311839939297280) }, { argument := 9389715551539451689697280, coefficient := (9389715551539451689697280) },
    { argument := 77999474771510519671029760, coefficient := (77999474771510519671029760) }, { argument := 2784808702309040409454575616, coefficient := (2784808702309040409454575616) },
    { argument := 2785460176746119572834222080, coefficient := (2785460176746119572834222080) }, { argument := 77204327868213269448622080, coefficient := (77204327868213269448622080) },
    { argument := 77999474771510519671029760, coefficient := (77999474771510519671029760) }, { argument := 2784808702309040409454575616, coefficient := (2784808702309040409454575616) },
    { argument := 2785460176746119572834222080, coefficient := (2785460176746119572834222080) }, { argument := 77204327868213269448622080, coefficient := (77204327868213269448622080) },
    { argument := 84589305240456301849346048, coefficient := (84589305240456301849346048) }, { argument := 3268914641396336806508625920, coefficient := (3268914641396336806508625920) },
    { argument := 3269720912449670640429957120, coefficient := (3269720912449670640429957120) }, { argument := 84046703862950741128773632, coefficient := (84046703862950741128773632) },
    { argument := 849932301854252720468262912, coefficient := (849932301854252720468262912) }, { argument := 3029797092350329451968462848, coefficient := (3029797092350329451968462848) },
    { argument := 849970923812959600276144128, coefficient := (849970923812959600276144128) }, { argument := 6021340351084089657109340225536, coefficient := (-6021340351084089657109340225536) },
    { argument := 42859901294215865932185600, coefficient := (42859901294215865932185600) }, { argument := 2115920134193883092353024000, coefficient := (2115920134193883092353024000) },
    { argument := 2115640410306779550549278720, coefficient := (2115640410306779550549278720) }, { argument := 42955887503865931334942720, coefficient := (42955887503865931334942720) },
    { argument := 7952739125473039299379200, coefficient := (7952739125473039299379200) }, { argument := 203115623086642040099831808, coefficient := (203115623086642040099831808) },
    { argument := 2653052104489133369651625984, coefficient := (2653052104489133369651625984) }, { argument := 202762799406118702323597312, coefficient := (202762799406118702323597312) },
    { argument := 7873162721473195489099776, coefficient := (7873162721473195489099776) }, { argument := 1530223459246088645467176960, coefficient := (1530223459246088645467176960) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form after bounded power-of-two normalization. -/
def form : Form := Form.normalizePowersOfTwo rawForm

theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by rfl

theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by decide +kernel

noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard13

namespace TermShard14

/-! Directed signed-log shard 14.  The untrusted producer supplies only integer arrays and
rational endpoints; the committed generic checker proves the direction of every logarithm. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-76973086038367755874898402082816)
def positiveArguments : Array ℕ := #[
    268388045974525, 268352565170567, 5448620920967, 360805826259, 18429348826521, 240699587552805,
    4599349992177, 89300716635, 4758404925, 5436445815285, 5437717610175, 37679172075,
    5437717610175, 268450832316375, 268415343212085, 5449895564085, 9425534502189, 240699587552805,
    196450159626831, 120141926846171, 1166470578753, 234914325125, 268388045974525, 268450832316375,
    1860156379875, 37679172075, 1860156379875, 1859910467865, 37763555865, 360179085501,
    4599349992177, 120141926846171, 4591375426227, 11143182377, 234883269535, 268352565170567,
    268415343212085, 1859910467865, 874096653, 89300716635, 1166470578753, 11143182377,
    432671229, 4769061535, 5448620920967, 5449895564085, 37763555865, 13443784695,
    663696692175, 663608951709, 13473892509, 22085860815, 1090341231975, 1090197089253,
    22135322853, 13443784695, 22085860815, 4856609275575, 176005020585, 821103825,
    4856609275575, 239762506207375, 239730809689565
  ]
def positiveCoefficients : Array ℕ := #[
    75544518990097896186472038400, 75534532031630142785246461952, 1533650446834379371002724352, 203115623086642040099831808, 5187400531737553958156107776, 67750910800690292199606190080,
    5178407727728707723170152448, 201087337080652126727700480, 42859901294215865932185600, 1530223459246088645467176960, 1530581437683132126776524800, 42422976329149699640524800,
    1530581437683132126776524800, 75562191774207872222625792000, 75552202479404362430687477760, 1534009226976332818950389760, 2653052104489133369651625984, 67750910800690292199606190080,
    884732865692270549133139378176, 67633892121998638163376996352, 2626658231905328804338335744, 2115920134193883092353024000, 75544518990097896186472038400, 75562191774207872222625792000,
    2094349894813975201185792000, 42422976329149699640524800, 2094349894813975201185792000, 2094073022504824718764277760, 42517984030449727187189760, 202762799406118702323597312,
    5178407727728707723170152448, 67633892121998638163376996352, 5169429164668492361811099648, 200737728003114711507795968, 2115640410306779550549278720, 75534532031630142785246461952,
    75552202479404362430687477760, 2094073022504824718764277760, 7873162721473195489099776, 201087337080652126727700480, 2626658231905328804338335744, 200737728003114711507795968,
    7794311942793338170638336, 42955887503865931334942720, 1533650446834379371002724352, 1534009226976332818950389760, 42517984030449727187189760, 3784088983928198576209920,
    186814010972897549274316800, 186789314227273617169711104, 3792563580172657338875904, 99465874536590639093514240, 4910460366029297538406809600, 4909811204920210169410879488,
    99688631752496424406745088, 3784088983928198576209920, 99465874536590639093514240, 1367013982735229032543027200, 99082018140242809737707520, 3697922880302488957747200,
    1367013982735229032543027200, 67487145850809392759308288000, 67478224074197014116187504640
  ]
def positiveScales : Array ℕ := #[
    47, 47, 42, 38, 44, 47,
    42, 36, 32, 42, 42, 35,
    42, 47, 47, 42, 43, 47,
    47, 46, 40, 37, 47, 47,
    40, 35, 40, 40, 35, 38,
    42, 46, 42, 33, 37, 47,
    47, 40, 29, 36, 40, 33,
    28, 32, 42, 42, 35, 33,
    39, 39, 33, 34, 39, 39,
    34, 33, 34, 42, 37, 29,
    42, 47, 47
  ]
def negativeArguments : Array ℕ := #[
    23
  ]
def negativeCoefficients : Array ℕ := #[
    1822247737828079764651510857728
  ]
def negativeScales : Array ℕ := #[
    4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    47931313743169315, 47931123006793060, 42309028259868301, 38392431679048015, 44067070329933221, 47774226998105529,
    42064567123877820, 36377952701841757, 32147830899694803, 42305800907691165, 42306138370375403, 35133048213813321,
    42306138370375403, 47931651205850823, 47931460469474576, 42309365722552538, 43099711571543454, 47774226998105529,
    47481156668491202, 46771733035625910, 40085287058124396, 37773343735617877, 47931313743169315, 47931651205850823,
    40758561049742627, 35133048213813321, 40758561049742627, 40758370313364905, 35136275565990457, 38389923454544299,
    42064567123877820, 46771733035625910, 42062063541382915, 33375442259096837, 37773152999240179, 47931123006793060,
    47931460469474576, 40758370313364905, 29703217573252635, 36377952701841757, 40085287058124396, 33375442259096837,
    28688695949282013, 32151058251871938, 42309028259868301, 42309365722552538, 35136275565990457, 33646220291755706,
    39271733127703010, 39271542391325220, 33649447643932738, 34362404012600087, 39987916847343556, 39987726110969461,
    34365631364777223, 33646220291755706, 34362404012600087, 42143086561830043, 37356825626429093, 29612989415135840,
    42143086561830043, 47768599397755321, 47768408661377614
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    4523561956057598
  ]

abbrev PositiveTerm := Fin 63
abbrev NegativeTerm := Fin 1
def positiveArgument (term : PositiveTerm) : ℕ := positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ := positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ := positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ := negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ := negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ := negativeScales[term.val]?.getD 0
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

noncomputable def positiveExact : ℝ := Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ := Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 1119158821 / 1000000000000
noncomputable def negativeCeiling : ℝ := 3100691 / 31250000000

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
  norm_num [positiveRationalLower, positiveFloor, bits, positiveLogLower, logBoundDenominator,
    positiveLogLowerNumerator, positiveLogLowerNumerators, positiveCoefficient,
    positiveCoefficients, Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [negativeRationalUpper, negativeCeiling, bits, negativeLogUpper, logBoundDenominator,
    negativeLogUpperNumerator, negativeLogUpperNumerators, negativeCoefficient,
    negativeCoefficients, Fin.sum_univ_succ, mass]

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
def rawForm : Form := { constantNumerator := 0, terms := [
    { argument := 75544518990097896186472038400, coefficient := (75544518990097896186472038400) }, { argument := 75534532031630142785246461952, coefficient := (75534532031630142785246461952) },
    { argument := 1533650446834379371002724352, coefficient := (1533650446834379371002724352) }, { argument := 203115623086642040099831808, coefficient := (203115623086642040099831808) },
    { argument := 5187400531737553958156107776, coefficient := (5187400531737553958156107776) }, { argument := 67750910800690292199606190080, coefficient := (67750910800690292199606190080) },
    { argument := 5178407727728707723170152448, coefficient := (5178407727728707723170152448) }, { argument := 201087337080652126727700480, coefficient := (201087337080652126727700480) },
    { argument := 42859901294215865932185600, coefficient := (42859901294215865932185600) }, { argument := 1530223459246088645467176960, coefficient := (1530223459246088645467176960) },
    { argument := 1530581437683132126776524800, coefficient := (1530581437683132126776524800) }, { argument := 42422976329149699640524800, coefficient := (42422976329149699640524800) },
    { argument := 1530581437683132126776524800, coefficient := (1530581437683132126776524800) }, { argument := 75562191774207872222625792000, coefficient := (75562191774207872222625792000) },
    { argument := 75552202479404362430687477760, coefficient := (75552202479404362430687477760) }, { argument := 1534009226976332818950389760, coefficient := (1534009226976332818950389760) },
    { argument := 2653052104489133369651625984, coefficient := (2653052104489133369651625984) }, { argument := 67750910800690292199606190080, coefficient := (67750910800690292199606190080) },
    { argument := 884732865692270549133139378176, coefficient := (884732865692270549133139378176) }, { argument := 67633892121998638163376996352, coefficient := (67633892121998638163376996352) },
    { argument := 2626658231905328804338335744, coefficient := (2626658231905328804338335744) }, { argument := 2115920134193883092353024000, coefficient := (2115920134193883092353024000) },
    { argument := 75544518990097896186472038400, coefficient := (75544518990097896186472038400) }, { argument := 75562191774207872222625792000, coefficient := (75562191774207872222625792000) },
    { argument := 2094349894813975201185792000, coefficient := (2094349894813975201185792000) }, { argument := 42422976329149699640524800, coefficient := (42422976329149699640524800) },
    { argument := 2094349894813975201185792000, coefficient := (2094349894813975201185792000) }, { argument := 2094073022504824718764277760, coefficient := (2094073022504824718764277760) },
    { argument := 42517984030449727187189760, coefficient := (42517984030449727187189760) }, { argument := 202762799406118702323597312, coefficient := (202762799406118702323597312) },
    { argument := 5178407727728707723170152448, coefficient := (5178407727728707723170152448) }, { argument := 67633892121998638163376996352, coefficient := (67633892121998638163376996352) },
    { argument := 5169429164668492361811099648, coefficient := (5169429164668492361811099648) }, { argument := 200737728003114711507795968, coefficient := (200737728003114711507795968) },
    { argument := 2115640410306779550549278720, coefficient := (2115640410306779550549278720) }, { argument := 75534532031630142785246461952, coefficient := (75534532031630142785246461952) },
    { argument := 75552202479404362430687477760, coefficient := (75552202479404362430687477760) }, { argument := 2094073022504824718764277760, coefficient := (2094073022504824718764277760) },
    { argument := 7873162721473195489099776, coefficient := (7873162721473195489099776) }, { argument := 201087337080652126727700480, coefficient := (201087337080652126727700480) },
    { argument := 2626658231905328804338335744, coefficient := (2626658231905328804338335744) }, { argument := 200737728003114711507795968, coefficient := (200737728003114711507795968) },
    { argument := 7794311942793338170638336, coefficient := (7794311942793338170638336) }, { argument := 42955887503865931334942720, coefficient := (42955887503865931334942720) },
    { argument := 1533650446834379371002724352, coefficient := (1533650446834379371002724352) }, { argument := 1534009226976332818950389760, coefficient := (1534009226976332818950389760) },
    { argument := 42517984030449727187189760, coefficient := (42517984030449727187189760) }, { argument := 1822247737828079764651510857728, coefficient := (-1822247737828079764651510857728) },
    { argument := 3784088983928198576209920, coefficient := (3784088983928198576209920) }, { argument := 186814010972897549274316800, coefficient := (186814010972897549274316800) },
    { argument := 186789314227273617169711104, coefficient := (186789314227273617169711104) }, { argument := 3792563580172657338875904, coefficient := (3792563580172657338875904) },
    { argument := 99465874536590639093514240, coefficient := (99465874536590639093514240) }, { argument := 4910460366029297538406809600, coefficient := (4910460366029297538406809600) },
    { argument := 4909811204920210169410879488, coefficient := (4909811204920210169410879488) }, { argument := 99688631752496424406745088, coefficient := (99688631752496424406745088) },
    { argument := 3784088983928198576209920, coefficient := (3784088983928198576209920) }, { argument := 99465874536590639093514240, coefficient := (99465874536590639093514240) },
    { argument := 1367013982735229032543027200, coefficient := (1367013982735229032543027200) }, { argument := 99082018140242809737707520, coefficient := (99082018140242809737707520) },
    { argument := 3697922880302488957747200, coefficient := (3697922880302488957747200) }, { argument := 1367013982735229032543027200, coefficient := (1367013982735229032543027200) },
    { argument := 67487145850809392759308288000, coefficient := (67487145850809392759308288000) }, { argument := 67478224074197014116187504640, coefficient := (67478224074197014116187504640) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form after bounded power-of-two normalization. -/
def form : Form := Form.normalizePowersOfTwo rawForm

theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by rfl

theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by decide +kernel

noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard14

namespace TermShard15

/-! Directed signed-log shard 15.  The untrusted producer supplies only integer arrays and
rational endpoints; the committed generic checker proves the direction of every logarithm. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-22901814639726415379587150118912)
def positiveArguments : Array ℕ := #[
    4867485817565, 663696692175, 1090341231975, 239762506207375, 8689067299025, 40536493625,
    176005020585, 8689067299025, 8687918607427, 176399189827, 663608951709, 1090197089253,
    239730809689565, 8687918607427, 40531134715, 821103825, 40536493625, 40531134715,
    822942715, 13473892509, 22135322853, 4867485817565, 176399189827, 822942715
  ]
def positiveCoefficients : Array ℕ := #[
    1370075457138556754607472640, 186814010972897549274316800, 4910460366029297538406809600, 67487145850809392759308288000, 4891510031260769017711820800, 182560137584456486617088000,
    99082018140242809737707520, 4891510031260769017711820800, 4890863375379179465263284224, 99303915696666823595393024, 186789314227273617169711104, 4909811204920210169410879488,
    67478224074197014116187504640, 4890863375379179465263284224, 182536003199377374592368640, 3697922880302488957747200, 182560137584456486617088000, 182536003199377374592368640,
    3706204504621264289136640, 3792563580172657338875904, 99688631752496424406745088, 1370075457138556754607472640, 99303915696666823595393024, 3706204504621264289136640
  ]
def positiveScales : Array ℕ := #[
    42, 39, 39, 47, 42, 35,
    37, 42, 42, 37, 39, 39,
    47, 42, 35, 29, 35, 35,
    29, 33, 34, 42, 37, 29
  ]
def negativeArguments : Array ℕ := #[
    1
  ]
def negativeCoefficients : Array ℕ := #[
    316912650057057350374175801344
  ]
def negativeScales : Array ℕ := #[
    0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    42146313914007179, 39271733127703010, 39987916847343556, 47768599397755321, 42982338461276398, 35238502251082444,
    37356825626429093, 42982338461276398, 42982147724902006, 37360052978606229, 39271542391325220, 39987726110969461,
    47768408661377614, 42982147724902006, 35238311514704653, 29612989415135840, 35238502251082444, 35238311514704653,
    29616216767312930, 33649447643932738, 34365631364777223, 42146313914007179, 37360052978606229, 29616216767312930
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0
  ]

abbrev PositiveTerm := Fin 24
abbrev NegativeTerm := Fin 1
def positiveArgument (term : PositiveTerm) : ℕ := positiveArguments[term.val]?.getD 0
def positiveCoefficient (term : PositiveTerm) : ℕ := positiveCoefficients[term.val]?.getD 0
def positiveScale (term : PositiveTerm) : ℕ := positiveScales[term.val]?.getD 0
def negativeArgument (term : NegativeTerm) : ℕ := negativeArguments[term.val]?.getD 0
def negativeCoefficient (term : NegativeTerm) : ℕ := negativeCoefficients[term.val]?.getD 0
def negativeScale (term : NegativeTerm) : ℕ := negativeScales[term.val]?.getD 0
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

noncomputable def positiveExact : ℝ := Form.natLogSum bits positiveArgument positiveCoefficient
noncomputable def negativeExact : ℝ := Form.natLogSum bits negativeArgument negativeCoefficient
noncomputable def positiveRationalLower : ℝ :=
  ∑ term, mass bits (positiveCoefficient term) * positiveLogLower term
noncomputable def negativeRationalUpper : ℝ :=
  ∑ term, mass bits (negativeCoefficient term) * negativeLogUpper term
noncomputable def positiveFloor : ℝ := 94510387 / 1000000000000
noncomputable def negativeCeiling : ℝ := 0 / 1

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
  norm_num [positiveRationalLower, positiveFloor, bits, positiveLogLower, logBoundDenominator,
    positiveLogLowerNumerator, positiveLogLowerNumerators, positiveCoefficient,
    positiveCoefficients, Fin.sum_univ_succ, mass]

theorem negativeRationalUpper_le_ceiling : negativeRationalUpper ≤ negativeCeiling := by
  norm_num [negativeRationalUpper, negativeCeiling, bits, negativeLogUpper, logBoundDenominator,
    negativeLogUpperNumerator, negativeLogUpperNumerators, negativeCoefficient,
    negativeCoefficients, Fin.sum_univ_succ, mass]

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
def rawForm : Form := { constantNumerator := 0, terms := [
    { argument := 1370075457138556754607472640, coefficient := (1370075457138556754607472640) }, { argument := 186814010972897549274316800, coefficient := (186814010972897549274316800) },
    { argument := 4910460366029297538406809600, coefficient := (4910460366029297538406809600) }, { argument := 67487145850809392759308288000, coefficient := (67487145850809392759308288000) },
    { argument := 4891510031260769017711820800, coefficient := (4891510031260769017711820800) }, { argument := 182560137584456486617088000, coefficient := (182560137584456486617088000) },
    { argument := 99082018140242809737707520, coefficient := (99082018140242809737707520) }, { argument := 4891510031260769017711820800, coefficient := (4891510031260769017711820800) },
    { argument := 4890863375379179465263284224, coefficient := (4890863375379179465263284224) }, { argument := 99303915696666823595393024, coefficient := (99303915696666823595393024) },
    { argument := 186789314227273617169711104, coefficient := (186789314227273617169711104) }, { argument := 4909811204920210169410879488, coefficient := (4909811204920210169410879488) },
    { argument := 67478224074197014116187504640, coefficient := (67478224074197014116187504640) }, { argument := 4890863375379179465263284224, coefficient := (4890863375379179465263284224) },
    { argument := 182536003199377374592368640, coefficient := (182536003199377374592368640) }, { argument := 3697922880302488957747200, coefficient := (3697922880302488957747200) },
    { argument := 182560137584456486617088000, coefficient := (182560137584456486617088000) }, { argument := 182536003199377374592368640, coefficient := (182536003199377374592368640) },
    { argument := 3706204504621264289136640, coefficient := (3706204504621264289136640) }, { argument := 3792563580172657338875904, coefficient := (3792563580172657338875904) },
    { argument := 99688631752496424406745088, coefficient := (99688631752496424406745088) }, { argument := 1370075457138556754607472640, coefficient := (1370075457138556754607472640) },
    { argument := 99303915696666823595393024, coefficient := (99303915696666823595393024) }, { argument := 3706204504621264289136640, coefficient := (3706204504621264289136640) },
    { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }] }

/-- Raw term shards carry no independent rational constant. -/
@[simp] theorem rawForm_constant : rawForm.constantNumerator = 0 := rfl

/-- Exact source-order form after bounded power-of-two normalization. -/
def form : Form := Form.normalizePowersOfTwo rawForm

theorem form_eval_rawForm : Form.eval bits form = Form.eval bits rawForm := by
  unfold form
  exact Form.eval_normalizePowersOfTwo bits rawForm

theorem signedForm_constant : signedForm.constantNumerator = form.constantNumerator := by rfl

theorem signedForm_terms_perm : signedForm.terms.Perm form.terms := by decide +kernel

noncomputable def lower : ℝ :=
  (constantNumerator : ℝ) / (2 : ℝ) ^ bits + positiveFloor - negativeCeiling

noncomputable def signedCertificate : LowerBound bits :=
  LowerBound.ofSignedFamilies bits constantNumerator positiveArgument positiveCoefficient
    negativeArgument negativeCoefficient positiveFloor negativeCeiling
      positiveFloor_le_exact negativeExact_le_ceiling

noncomputable def certificate : LowerBound bits :=
  LowerBound.reorder signedCertificate form signedForm_constant signedForm_terms_perm

@[simp] theorem certificate_form : certificate.form = form := rfl

@[simp] theorem certificate_lower : certificate.lower = lower := by
  simp [certificate, LowerBound.reorder, signedCertificate, LowerBound.ofSignedFamilies, lower,
    constantNumerator, bits]

end TermShard15

end MatrixMultiplication.Generated.TotalQuotientOuterFloorRoot.Region0.Branch1
