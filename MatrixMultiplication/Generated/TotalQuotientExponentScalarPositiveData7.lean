import MatrixMultiplication.DyadicLogLinear

/-! Generated compressed retained-exponent log chunk; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive7

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def arguments : Array ℕ := #[
    1687, 1689, 1695, 1699, 1701, 1711,
    1713, 1715, 1719, 1721, 1723, 1727,
    1729, 1731, 1733, 1735, 1739, 1743,
    1745, 1749, 1753, 1755, 1757, 1759,
    1761, 1765, 1767, 1771, 1775, 1779,
    1781, 1783, 1797, 1803, 1805, 1809,
    1811, 1813, 1815, 1817, 1819, 1827,
    1833, 1837, 1847, 1849, 1851, 1855,
    1857, 1861, 1865, 1869, 1873, 1881,
    1883, 1885, 1889, 1897, 1899, 1903,
    1905, 1907, 1909, 1911
  ]

def coefficients : Array ℕ := #[
    549755813888, 580915801620480, 132714489446400, 481556028194816, 292160855343104, 8864812498944,
    117699283779584, 619525410127872, 104084237451264, 18029198966784, 360777252864, 33603824123904,
    217424129425408, 1315045434720256, 238147346628608, 1322849927168, 412831182749696, 1557245619863552,
    171798691840, 60095182405632, 187067300577280, 723590320226304, 17179869184, 33328946216960,
    137438953472, 14441827532800, 42004780154880, 8091937428996096, 56461640073216, 34359738368,
    19366007537664, 8034017110654976, 171798691840, 549755813888, 32195074850816, 274877906944,
    274877906944, 601295421440, 1683627180032, 747324309504, 648338198233088, 10402410790912,
    316461780303872, 950407543128064, 309237645312, 206158430208, 584115552256, 549755813888,
    257698037760, 124023623122944, 74062416052224, 4640365344718848, 233130824826880, 137438953472,
    1786706395136, 1821066133504, 31907312041984, 16389595201536, 11250666831872, 986193210638336,
    14431090114560, 302322747965440, 171798691840, 26691074260992
  ]

def scales : Array ℕ := #[
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10, 10, 10,
    10, 10, 10, 10
  ]

abbrev Term := Fin 64
def argument (term : Term) : ℕ := arguments[term.val]?.getD 0
def coefficient (term : Term) : ℕ := coefficients[term.val]?.getD 0
def scale (term : Term) : ℕ := scales[term.val]?.getD 0

theorem arguments_pos : ∀ term, 0 < argument term := by decide
theorem scales_valid : ∀ term, 2 ^ scale term ≤ argument term := by decide

noncomputable def exact : ℝ := logSum 55 argument coefficient
noncomputable def fastLower : ℝ :=
  fastLogSumLowerWithScale 8 55 argument coefficient scale
noncomputable def floor : ℝ := 4771766223657 / 500000000000

theorem floor_le_fast : floor ≤ fastLower := by
  norm_num [floor, fastLower, fastLogSumLowerWithScale, fastLogSumUpperWithScale,
    argument, coefficient, scale, arguments, coefficients, scales,
    MatrixMultiplication.FastDyadicLog.numeratorLogLower,
    MatrixMultiplication.FastDyadicLog.numeratorLogUpper,
    MatrixMultiplication.FastDyadicLog.fastLogTwoLower,
    MatrixMultiplication.FastDyadicLog.fastLogTwoUpper,
    reducedArgument,
    AlgebraicComplexity.Analysis.logRatioLower,
    AlgebraicComplexity.Analysis.logRatioUpper,
    AlgebraicComplexity.Analysis.atanhPartial,
    AlgebraicComplexity.Analysis.atanhRemainder, Fin.sum_univ_succ,
    Finset.sum_range_succ, mass]

theorem exact_bound : floor ≤ exact := by
  exact floor_le_fast.trans (fastLogSumLowerWithScale_le_logSum 8 55 argument coefficient scale scales_valid)

end MatrixMultiplication.Generated.TotalQuotientExponentScalar.Positive7
