import SpectralRadiusUpperTail.RealSchurCanonicalDiagonalGap
import SpectralRadiusUpperTail.RealSchurNativeGapKernel
import SpectralRadiusUpperTail.SchurGapLawScaling

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix

theorem realSchurPairFromCoordinates_scale (u g c : ℝ) (hc : 0 < c) :
    realSchurPairFromCoordinates (u/c) (g/c)=
      ((realSchurPairFromCoordinates u g).1/Real.sqrt c,
       (realSchurPairFromCoordinates u g).2/Real.sqrt c) := by
  have he : g/c+4*(u/c)=(g+4*u)/c := by ring
  unfold realSchurPairFromCoordinates
  rw [he,Real.sqrt_div' _ hc.le,Real.sqrt_div' _ hc.le]
  apply Prod.ext <;> dsimp only <;> ring

theorem realSchurNativeCanonicalEntries_scale (q : ℕ) (x u g c : ℝ) (hc : 0 < c) :
    realSchurNativeCanonicalEntries q (x/Real.sqrt c,u/c,g/c)=
      fun ij => realSchurNativeCanonicalEntries q (x,u,g) ij/Real.sqrt c := by
  funext ij
  unfold realSchurNativeCanonicalEntries
  rw [realSchurPairFromCoordinates_scale u g c hc]
  split_ifs <;> simp only [Prod.fst,Prod.snd,neg_div]

theorem realSchurNativeGapLaw_map_div (q : ℕ) (n u c : ℝ)
    (hn : 0 < n) (hu : q=2 → 0 < u) (hc : 0 < c) :
    (realSchurNativeGapLaw q n u).map (fun g : ℝ => g/c)=
      realSchurNativeGapLaw q (n*c) (u/c) := by
  by_cases hq : q=2
  · simp only [realSchurNativeGapLaw,hq,ite_true]
    rw [schurSquaredGapLaw_map_div n (Real.sqrt u) c hn (Real.sqrt_pos.mpr (hu hq)) hc,
      Real.sqrt_div' _ hc.le]
  · simp [realSchurNativeGapLaw,hq,Measure.map_dirac]

#print axioms realSchurPairFromCoordinates_scale
#print axioms realSchurNativeCanonicalEntries_scale
#print axioms realSchurNativeGapLaw_map_div
end SpectralRadiusUpperTail
