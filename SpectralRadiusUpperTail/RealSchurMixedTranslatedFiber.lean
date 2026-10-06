import SpectralRadiusUpperTail.RealSchurMixedGaussianFiber
import SpectralRadiusUpperTail.RealSchurMixedUpperEnergy
import SpectralRadiusUpperTail.RealSchurMixedUpperGaussianIntegral
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix BigOperators

/-- In independent block-entry coordinates, adding a block-upper chart
center merely translates each diagonal and strictly-upper coordinate. -/
theorem realSchurMixed_translatedFiber_eq_join
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T = 0)
    (ω : RealSchurMixedOrbitIndex s → ℝ)
    (d : RealSchurMixedDiagonalEntry s → ℝ)
    (u : RealSchurMixedStrictUpperEntry s → ℝ) :
    T + (realSchurMixedFiberPoint s ω d u).2.val =
      realSchurMixedUpperEntryJoin s
        (fun p => T p.1.1 p.1.2 + d p)
        (fun p => T p.1.1 p.1.2 + u p) := by
  ext a b
  rw [realSchurMixedFiberPoint_upper]
  by_cases hd : a.1 = b.1
  · simp [realSchurMixedUpperEntryJoin, hd]
  by_cases hu : a.1 < b.1
  · simp [realSchurMixedUpperEntryJoin, hd, hu]
  have hl : b.1 < a.1 := by omega
  have hzero : T a b = 0 :=
    (realSchurMixed_blockTriangular_iff_lower_zero s T).mpr hT hl
  simp [realSchurMixedUpperEntryJoin, hd, hu, hzero]

/-- At any block-upper center, the Gaussian weight is a product of a
translated diagonal-block density and a translated strict-upper density. -/
theorem realSchurMixedGaussianWeight_translatedFiber
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T = 0)
    (ω : RealSchurMixedOrbitIndex s → ℝ)
    (d : RealSchurMixedDiagonalEntry s → ℝ)
    (u : RealSchurMixedStrictUpperEntry s → ℝ) :
    realMatrixGaussianWeight (RealSchurMixedCoord s)
      (T + (realSchurMixedFiberPoint s ω d u).2.val) =
      Real.exp (-(∑ p : RealSchurMixedDiagonalEntry s,
        (T p.1.1 p.1.2 + d p)^2)/2) *
      Real.exp (-(∑ p : RealSchurMixedStrictUpperEntry s,
        (T p.1.1 p.1.2 + u p)^2)/2) := by
  rw [realSchurMixed_translatedFiber_eq_join s T hT ω d u,
    realSchurMixedGaussianWeight_join]

/-- A whole strictly-upper fiber has the same Gaussian normalizer at
every block-upper chart center. Only the diagonal-block Gaussian factor
survives. -/
theorem realSchurMixedGaussianWeight_integral_translatedFiber
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T = 0)
    (ω : RealSchurMixedOrbitIndex s → ℝ)
    (d : RealSchurMixedDiagonalEntry s → ℝ) :
    (∫ u : RealSchurMixedStrictUpperEntry s → ℝ,
      realMatrixGaussianWeight (RealSchurMixedCoord s)
        (T + (realSchurMixedFiberPoint s ω d u).2.val)) =
      Real.exp (-(∑ p : RealSchurMixedDiagonalEntry s,
        (T p.1.1 p.1.2 + d p)^2)/2) *
      (Real.sqrt (2*Real.pi)) ^
        (Fintype.card (RealSchurMixedStrictUpperEntry s)) := by
  simp_rw [realSchurMixedGaussianWeight_translatedFiber s T hT ω d]
  rw [integral_const_mul,
    realSchurMixedIndependentGaussianIntegral_shift _
      (fun p : RealSchurMixedStrictUpperEntry s => T p.1.1 p.1.2)]

#print axioms realSchurMixedGaussianWeight_translatedFiber
#print axioms realSchurMixedGaussianWeight_integral_translatedFiber
end SpectralRadiusUpperTail
