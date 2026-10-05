import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 13, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13

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
def constantNumerator : ℤ := (-277265998082659189259922509020528640)
def positiveArguments : Array ℕ := #[
    405, 711, 27, 225, 27, 711,
    1413, 225, 21807, 1395, 405, 711,
    27, 1395, 27, 711, 711, 27,
    27, 123, 3, 1287, 57, 3,
    57, 111, 2097, 111, 1287, 2097,
    27, 111, 111, 123, 399, 38528875371,
    38528877717, 88423159039, 646418212003, 176842092895, 12391294533, 121657533923,
    243315102981, 12391389221, 30178103, 3008100783, 62381294219, 6016209833,
    30178103, 14970921, 2862321623, 2862321721, 14970823
  ]
def positiveCoefficients : Array ℕ := #[
    31335357244411188208384081920, 55010960495744085965829832704, 2089023816294079213892272128, 34817063604901320231537868800, 2089023816294079213892272128, 55010960495744085965829832704,
    54662789859695072763514454016, 34817063604901320231537868800, 843617451146758989210162561024, 53966448587597046358883696640, 31335357244411188208384081920, 55010960495744085965829832704,
    2089023816294079213892272128, 53966448587597046358883696640, 2089023816294079213892272128, 55010960495744085965829832704, 55010960495744085965829832704, 2089023816294079213892272128,
    4178047632588158427784544256, 4758332026003180431643508736, 3713820117856140824697372672, 49788400955008887931099152384, 4410161389954167229328130048, 3713820117856140824697372672,
    4410161389954167229328130048, 4294104511271162828556337152, 162247516398840152278966468608, 4294104511271162828556337152, 49788400955008887931099152384, 162247516398840152278966468608,
    4178047632588158427784544256, 4294104511271162828556337152, 4294104511271162828556337152, 4758332026003180431643508736, 31612036843191470699824036184064, 363894939349344333754959692562432,
    363894961506687871379335035224064, 835133125110451415672293097996288, 3052623698279491787560335167193088, 835113172247868225056120158289920, 58516233982005072888120861523968, 2298045842346208243888782816837632,
    2298046174186900995138751983255552, 58516681133442602849086855970816, 285024124247575777664749797376, 56821417258932543417004559695872, 589174665955671122999430608846848, 56821495338539971183718522945536,
    285024124247575777664749797376, 70698175548089311792270934016, 13516931695648244585500516548608, 13516932158440159906725747490816, 70697712756173990567039991808
  ]
def positiveScales : Array ℕ := #[
    8, 9, 4, 7, 4, 9,
    10, 7, 14, 10, 8, 9,
    4, 10, 4, 9, 9, 4,
    4, 6, 1, 10, 5, 1,
    5, 6, 11, 6, 10, 11,
    4, 6, 6, 6, 8, 35,
    35, 36, 39, 37, 33, 36,
    37, 33, 24, 31, 35, 32,
    24, 23, 31, 31, 23
  ]
def negativeArguments : Array ℕ := #[
    9, 3, 399, 4593, 59611, 1859,
    4439, 343
  ]
def negativeCoefficients : Array ℕ := #[
    1426106925256758076683791106048, 475368975085586025561263702016, 31612036843191470699824036184064, 727789900856032205134294727786496, 4722869995637811428288748423479296, 4713124931648556914764742517587968,
    703387626801638789155483191083008, 27175259742392667794585574965248
  ]
def negativeScales : Array ℕ := #[
    3, 1, 8, 12, 15, 10,
    12, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8661778097770205, 9473705749619407, 4754887502147955, 7813781191164178, 4754887502147955, 9473705749619407,
    10464545750333933, 7813781191164178, 14412503690893657, 10446049406716546, 8661778097770205, 9473705749619407,
    4754887502147955, 10446049406716546, 4754887502147955, 9473705749619407, 9473705749619407, 4754887502147955,
    4754887502147955, 6942514504772358, 1584962500720924, 10329796338220701, 5832890014087662, 1584962500720924,
    5832890014087662, 6794415866314396, 11034111146096592, 6794415866314396, 10329796338220701, 11034111146096592,
    4754887502147955, 6794415866314396, 6794415866314396, 6942514504772358, 8640244936221314, 35165221024298528,
    35165221112143357, 36363705226351378, 39233676888503363, 37363670757308163, 33528607864260080, 36824034708952352,
    37824034917279304, 33528618888563128, 24846998784802333, 31486205757670205, 35860394433227599, 32486207740109054,
    24846998784802333, 23835659641789767, 31414538642695635, 31414538692090543, 23835650197843296
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    3169925001442313, 1584962500724866, 8640244936238936, 12165221068220945, 15863290957114591, 10860311057025654,
    12116018993325094, 8422064766172829
  ]

abbrev PositiveTerm := Fin 53
abbrev NegativeTerm := Fin 8
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
noncomputable def positiveFloor : ℝ := 4915022405563 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1733210900431 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 31335357244411188208384081920, coefficient := 31335357244411188208384081920 }, { argument := 55010960495744085965829832704, coefficient := 55010960495744085965829832704 }, { argument := 2089023816294079213892272128, coefficient := 2089023816294079213892272128 }, { argument := 34817063604901320231537868800, coefficient := 34817063604901320231537868800 }, { argument := 2089023816294079213892272128, coefficient := 2089023816294079213892272128 }, { argument := 55010960495744085965829832704, coefficient := 55010960495744085965829832704 }, { argument := 54662789859695072763514454016, coefficient := 54662789859695072763514454016 }, { argument := 34817063604901320231537868800, coefficient := 34817063604901320231537868800 }, { argument := 843617451146758989210162561024, coefficient := 843617451146758989210162561024 }, { argument := 53966448587597046358883696640, coefficient := 53966448587597046358883696640 }, { argument := 31335357244411188208384081920, coefficient := 31335357244411188208384081920 }, { argument := 55010960495744085965829832704, coefficient := 55010960495744085965829832704 }, { argument := 2089023816294079213892272128, coefficient := 2089023816294079213892272128 }, { argument := 53966448587597046358883696640, coefficient := 53966448587597046358883696640 }, { argument := 2089023816294079213892272128, coefficient := 2089023816294079213892272128 }, { argument := 55010960495744085965829832704, coefficient := 55010960495744085965829832704 }, { argument := 55010960495744085965829832704, coefficient := 55010960495744085965829832704 }, { argument := 2089023816294079213892272128, coefficient := 2089023816294079213892272128 }, { argument := 1426106925256758076683791106048, coefficient := (-1426106925256758076683791106048) }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4758332026003180431643508736, coefficient := 4758332026003180431643508736 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 49788400955008887931099152384, coefficient := 49788400955008887931099152384 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 3713820117856140824697372672, coefficient := 3713820117856140824697372672 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 162247516398840152278966468608, coefficient := 162247516398840152278966468608 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 49788400955008887931099152384, coefficient := 49788400955008887931099152384 }, { argument := 162247516398840152278966468608, coefficient := 162247516398840152278966468608 }, { argument := 4178047632588158427784544256, coefficient := 4178047632588158427784544256 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4758332026003180431643508736, coefficient := 4758332026003180431643508736 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 31612036843191470699824036184064, coefficient := 31612036843191470699824036184064 }, { argument := 31612036843191470699824036184064, coefficient := (-31612036843191470699824036184064) }, { argument := 363894939349344333754959692562432, coefficient := 363894939349344333754959692562432 }, { argument := 363894961506687871379335035224064, coefficient := 363894961506687871379335035224064 }, { argument := 727789900856032205134294727786496, coefficient := (-727789900856032205134294727786496) }, { argument := 835133125110451415672293097996288, coefficient := 835133125110451415672293097996288 }, { argument := 3052623698279491787560335167193088, coefficient := 3052623698279491787560335167193088 }, { argument := 835113172247868225056120158289920, coefficient := 835113172247868225056120158289920 }, { argument := 4722869995637811428288748423479296, coefficient := (-4722869995637811428288748423479296) }, { argument := 58516233982005072888120861523968, coefficient := 58516233982005072888120861523968 }, { argument := 2298045842346208243888782816837632, coefficient := 2298045842346208243888782816837632 }, { argument := 2298046174186900995138751983255552, coefficient := 2298046174186900995138751983255552 }, { argument := 58516681133442602849086855970816, coefficient := 58516681133442602849086855970816 }, { argument := 4713124931648556914764742517587968, coefficient := (-4713124931648556914764742517587968) }, { argument := 285024124247575777664749797376, coefficient := 285024124247575777664749797376 }, { argument := 56821417258932543417004559695872, coefficient := 56821417258932543417004559695872 }, { argument := 589174665955671122999430608846848, coefficient := 589174665955671122999430608846848 }, { argument := 56821495338539971183718522945536, coefficient := 56821495338539971183718522945536 }, { argument := 285024124247575777664749797376, coefficient := 285024124247575777664749797376 }, { argument := 703387626801638789155483191083008, coefficient := (-703387626801638789155483191083008) }, { argument := 70698175548089311792270934016, coefficient := 70698175548089311792270934016 }, { argument := 13516931695648244585500516548608, coefficient := 13516931695648244585500516548608 }, { argument := 13516932158440159906725747490816, coefficient := 13516932158440159906725747490816 }, { argument := 70697712756173990567039991808, coefficient := 70697712756173990567039991808 }, { argument := 27175259742392667794585574965248, coefficient := (-27175259742392667794585574965248) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
