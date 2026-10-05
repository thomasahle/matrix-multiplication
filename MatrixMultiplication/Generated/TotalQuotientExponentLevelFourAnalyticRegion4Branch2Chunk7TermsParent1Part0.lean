import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 4, branch 2,
parent chunk 7, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk7

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
def constantNumerator : ℤ := (-1486392704045207118158424440832)
def positiveArguments : Array ℕ := #[
    17, 50331701, 50331595, 42199427, 150479339, 21101129,
    390115, 14289951, 228639261, 6241731, 106325, 7108765,
    86010851, 7108833, 222197
  ]
def positiveCoefficients : Array ℕ := #[
    5387515050969974956360988622848, 475369475656433209743656353792, 475368474514738841378871050240, 797124638644417374845055008768, 2842474347431916139685951307776, 797178114722469390707454902272,
    58952512014870132561312481280, 2159436340615986223715211804672, 2159436765628969681983281037312, 58951482538976866978655895552, 2008422465164460109384908800, 67140387141193666915079290880,
    812349519850990213796139630592, 67141029383035337186828353536, 2098591330788373115095220224
  ]
def positiveScales : Array ℕ := #[
    4, 25, 25, 25, 27, 24,
    18, 23, 27, 22, 16, 22,
    26, 22, 17
  ]
def negativeArguments : Array ℕ := #[
    1783839539937, 59632706501149, 721512070671371, 29816638463163, 1863925685633, 294040267561,
    344585211330165, 689170558266147, 18818245660083, 294040267561, 67082886775267, 18819234018269,
    1783839539937, 1783835442463, 1783835442463, 59632579397091, 721510554899445, 29816574911301,
    1863921377919, 67082886775267, 307192728496875, 2457542311949037, 8385215147643, 344585211330165,
    307192728496875, 344608631133663, 59632706501149, 59632579397091, 18819234018269, 344608631133663,
    43076087353887, 18818902359669, 689170558266147, 2457542311949037, 43076087353887, 721512070671371,
    721510554899445, 18818245660083, 8385215147643, 18818902359669, 29816638463163, 29816574911301,
    1863925685633, 1863921377919, 3, 7, 7, 3
  ]
def negativeCoefficients : Array ℕ := #[
    502106192959314388605468672, 16785114673604299418704543744, 203087593288681338207129829376, 16785275234017710665531129856, 524648438953942191857205248, 5296958557678562170869121024,
    193984228667989338788179476480, 193984266837633520692658962432, 5296865258907265770819944448, 5296958557678562170869121024, 18882153992751852202756145152, 5297143457004651907030974464,
    502106192959314388605468672, 502105039622915666086985728, 502105039622915666086985728, 16785078896992534038835101696, 203087166636813768690939985920, 16785239457499957927883046912,
    524647226440244365690404864, 18882153992751852202756145152, 691736528794726098901401600000, 691736665021306892038566838272, 18881825907173226700251070464, 193984228667989338788179476480,
    691736528794726098901401600000, 193997412845277674168024825856, 16785114673604299418704543744, 16785078896992534038835101696, 5297143457004651907030974464, 193997412845277674168024825856,
    193997450955544428260414717952, 5297050103407941018256932864, 193984266837633520692658962432, 691736665021306892038566838272, 193997450955544428260414717952, 203087593288681338207129829376,
    203087166636813768690939985920, 5296865258907265770819944448, 18881825907173226700251070464, 5297050103407941018256932864, 16785275234017710665531129856, 16785239457499957927883046912,
    524648438953942191857205248, 524647226440244365690404864, 950737950171172051122527404032, 4436777100798802905238461218816, 4436777100798802905238461218816, 950737950171172051122527404032
  ]
def negativeScales : Array ℕ := #[
    40, 45, 49, 44, 40, 38,
    48, 49, 44, 38, 45, 44,
    40, 40, 40, 45, 49, 44,
    40, 45, 48, 51, 42, 48,
    48, 48, 45, 45, 44, 48,
    45, 44, 49, 51, 45, 49,
    49, 44, 42, 44, 44, 44,
    40, 40, 1, 2, 2, 1
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4087462841250339, 25584964019900207, 25584960981540042, 25330720073810565, 27164990175861609, 24330816855519657,
    18573539945779301, 23768497633656102, 27768497917602450, 22573514752065185, 16698121329396187, 22761167512676323,
    26358015343751404, 22761181312934671, 17761479812683553
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    40698122986403758, 45761169050496681, 49358016859178437, 44761182850736372, 40761481480095286, 38097222783287020,
    48291854114726336, 49291854398600707, 44097197371938483, 38097222783287020, 45931010014750714, 44097273142126396,
    40698122986403758, 40698119672533824, 40698119672533824, 45761165975462837, 49358013828322784, 44761179775740023,
    40761478145882504, 45931010014750714, 48126137395114768, 51126137679230736, 42930984947080404, 48291854114726336,
    48126137395114768, 48291952164454283, 45761169050496681, 45761165975462837, 44097273142126396, 48291952164454283,
    45291952447867792, 44097247716732710, 49291854398600707, 51126137679230736, 45291952447867792, 49358016859178437,
    49358013828322784, 44097197371938483, 42930984947080404, 44097247716732710, 44761182850736372, 44761179775740023,
    40761481480095286, 40761478145882504, 1584962500724866, 2807354922807594, 2807354922807594, 1584962500724866
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
noncomputable def positiveFloor : ℝ := 453503979 / 125000000000
noncomputable def negativeCeiling : ℝ := 1750845979 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 502106192959314388605468672, coefficient := (-502106192959314388605468672) }, { argument := 16785114673604299418704543744, coefficient := (-16785114673604299418704543744) }, { argument := 203087593288681338207129829376, coefficient := (-203087593288681338207129829376) }, { argument := 16785275234017710665531129856, coefficient := (-16785275234017710665531129856) }, { argument := 524648438953942191857205248, coefficient := (-524648438953942191857205248) }, { argument := 5296958557678562170869121024, coefficient := (-5296958557678562170869121024) }, { argument := 193984228667989338788179476480, coefficient := (-193984228667989338788179476480) }, { argument := 193984266837633520692658962432, coefficient := (-193984266837633520692658962432) }, { argument := 5296865258907265770819944448, coefficient := (-5296865258907265770819944448) }, { argument := 5296958557678562170869121024, coefficient := (-5296958557678562170869121024) }, { argument := 18882153992751852202756145152, coefficient := (-18882153992751852202756145152) }, { argument := 5297143457004651907030974464, coefficient := (-5297143457004651907030974464) }, { argument := 502106192959314388605468672, coefficient := (-502106192959314388605468672) }, { argument := 502105039622915666086985728, coefficient := (-502105039622915666086985728) }, { argument := 502105039622915666086985728, coefficient := (-502105039622915666086985728) }, { argument := 16785078896992534038835101696, coefficient := (-16785078896992534038835101696) }, { argument := 203087166636813768690939985920, coefficient := (-203087166636813768690939985920) }, { argument := 16785239457499957927883046912, coefficient := (-16785239457499957927883046912) }, { argument := 524647226440244365690404864, coefficient := (-524647226440244365690404864) }, { argument := 18882153992751852202756145152, coefficient := (-18882153992751852202756145152) }, { argument := 691736528794726098901401600000, coefficient := (-691736528794726098901401600000) }, { argument := 691736665021306892038566838272, coefficient := (-691736665021306892038566838272) }, { argument := 18881825907173226700251070464, coefficient := (-18881825907173226700251070464) }, { argument := 193984228667989338788179476480, coefficient := (-193984228667989338788179476480) }, { argument := 691736528794726098901401600000, coefficient := (-691736528794726098901401600000) }, { argument := 193997412845277674168024825856, coefficient := (-193997412845277674168024825856) }, { argument := 16785114673604299418704543744, coefficient := (-16785114673604299418704543744) }, { argument := 16785078896992534038835101696, coefficient := (-16785078896992534038835101696) }, { argument := 5297143457004651907030974464, coefficient := (-5297143457004651907030974464) }, { argument := 193997412845277674168024825856, coefficient := (-193997412845277674168024825856) }, { argument := 193997450955544428260414717952, coefficient := (-193997450955544428260414717952) }, { argument := 5297050103407941018256932864, coefficient := (-5297050103407941018256932864) }, { argument := 193984266837633520692658962432, coefficient := (-193984266837633520692658962432) }, { argument := 691736665021306892038566838272, coefficient := (-691736665021306892038566838272) }, { argument := 193997450955544428260414717952, coefficient := (-193997450955544428260414717952) }, { argument := 203087593288681338207129829376, coefficient := (-203087593288681338207129829376) }, { argument := 203087166636813768690939985920, coefficient := (-203087166636813768690939985920) }, { argument := 5296865258907265770819944448, coefficient := (-5296865258907265770819944448) }, { argument := 18881825907173226700251070464, coefficient := (-18881825907173226700251070464) }, { argument := 5297050103407941018256932864, coefficient := (-5297050103407941018256932864) }, { argument := 16785275234017710665531129856, coefficient := (-16785275234017710665531129856) }, { argument := 16785239457499957927883046912, coefficient := (-16785239457499957927883046912) }, { argument := 524648438953942191857205248, coefficient := (-524648438953942191857205248) }, { argument := 524647226440244365690404864, coefficient := (-524647226440244365690404864) }, { argument := 5387515050969974956360988622848, coefficient := 5387515050969974956360988622848 }, { argument := 475369475656433209743656353792, coefficient := 475369475656433209743656353792 }, { argument := 475368474514738841378871050240, coefficient := 475368474514738841378871050240 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 797124638644417374845055008768, coefficient := 797124638644417374845055008768 }, { argument := 2842474347431916139685951307776, coefficient := 2842474347431916139685951307776 }, { argument := 797178114722469390707454902272, coefficient := 797178114722469390707454902272 }, { argument := 4436777100798802905238461218816, coefficient := (-4436777100798802905238461218816) }, { argument := 58952512014870132561312481280, coefficient := 58952512014870132561312481280 }, { argument := 2159436340615986223715211804672, coefficient := 2159436340615986223715211804672 }, { argument := 2159436765628969681983281037312, coefficient := 2159436765628969681983281037312 }, { argument := 58951482538976866978655895552, coefficient := 58951482538976866978655895552 }, { argument := 4436777100798802905238461218816, coefficient := (-4436777100798802905238461218816) }, { argument := 2008422465164460109384908800, coefficient := 2008422465164460109384908800 }, { argument := 67140387141193666915079290880, coefficient := 67140387141193666915079290880 }, { argument := 812349519850990213796139630592, coefficient := 812349519850990213796139630592 }, { argument := 67141029383035337186828353536, coefficient := 67141029383035337186828353536 }, { argument := 2098591330788373115095220224, coefficient := 2098591330788373115095220224 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region4.Branch2.Chunk7
