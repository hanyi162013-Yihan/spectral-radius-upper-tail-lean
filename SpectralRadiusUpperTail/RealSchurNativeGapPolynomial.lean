import SpectralRadiusUpperTail.RealSchurNativeSpectralCoordinates
import SpectralRadiusUpperTail.RealSchurDiagonalCharpoly

namespace SpectralRadiusUpperTail
open scoped Matrix

theorem realSchurNativeCanonicalEntries_continuous (q : ℕ) :
    Continuous (realSchurNativeCanonicalEntries q) := by
  apply continuous_pi
  intro ij
  unfold realSchurNativeCanonicalEntries
  split_ifs
  · exact continuous_fst
  · change Continuous (fun v : ℝ × (ℝ × ℝ) => (Real.sqrt (v.2.2+4*v.2.1)+Real.sqrt v.2.2)/2)
    fun_prop
  · change Continuous (fun v : ℝ × (ℝ × ℝ) => -((Real.sqrt (v.2.2+4*v.2.1)-Real.sqrt v.2.2)/2))
    fun_prop

theorem realPairGapBlockEntries_charpoly (x u s : ℝ) (hu : 0 < u) (hs : 0 < s) :
    (Matrix.of (realPairGapBlockEntries x (u,s)).curry).charpoly =
      Polynomial.X^2-Polynomial.C (2*x)*Polynomial.X+Polynomial.C (x^2+u) := by
  change (realSchurBlock x (realSchurPairFromCoordinates u s).1
    (realSchurPairFromCoordinates u s).2).charpoly=_
  rw [realSchurBlock_charpoly]
  have h := congrArg Prod.fst (realSchur_pair_chart_forward u s hu hs)
  change (realSchurPairFromCoordinates u s).1*(realSchurPairFromCoordinates u s).2=u at h
  rw [h]

theorem realSchurNativeCanonicalEntries_charpoly_gap (q : ℕ) (hq : q=1 ∨ q=2)
    (x u a b : ℝ) (hu : q=2 → 0 < u) (ha : q=2 → 0 < a) (hb : q=2 → 0 < b) :
    (Matrix.of (realSchurNativeCanonicalEntries q (x,u,a)).curry).charpoly=
      (Matrix.of (realSchurNativeCanonicalEntries q (x,u,b)).curry).charpoly := by
  rcases hq with rfl | rfl
  · rw [realSchurNativeCanonicalEntries_one,realSchurNativeCanonicalEntries_one]
  · rw [realSchurNativeCanonicalEntries_two,realSchurNativeCanonicalEntries_two,
      realPairGapBlockEntries_charpoly x u a (hu rfl) (ha rfl),
      realPairGapBlockEntries_charpoly x u b (hu rfl) (hb rfl)]

#print axioms realSchurNativeCanonicalEntries_continuous
#print axioms realPairGapBlockEntries_charpoly
#print axioms realSchurNativeCanonicalEntries_charpoly_gap
end SpectralRadiusUpperTail
