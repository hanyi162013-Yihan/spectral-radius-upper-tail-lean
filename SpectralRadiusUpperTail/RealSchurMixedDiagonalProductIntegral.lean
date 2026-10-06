import SpectralRadiusUpperTail.RealSchurMixedDiagonalProductVolume
import SpectralRadiusUpperTail.RealSchurMixedNativeDiagonal

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix BigOperators

theorem realSchurMixedDiagonal_energy_sum
    {m : ℕ} (s : Fin m → ℕ) (d : RealSchurMixedDiagonalEntry s → ℝ) :
    (∑ p : RealSchurMixedDiagonalEntry s, (d p)^2) =
      ∑ i : Fin m, ∑ ab : Fin (s i) × Fin (s i),
        (realSchurMixedDiagonalProductEquiv s d i ab)^2 := by
  rw [← (realSchurMixedDiagonalIndexEquiv s).sum_comp (fun p => (d p)^2),Fintype.sum_sigma]
  rfl

theorem realSchurMixedDiagonal_gaussian_product
    {m : ℕ} (s : Fin m → ℕ) (d : RealSchurMixedDiagonalEntry s → ℝ) :
    Real.exp (-(∑ p : RealSchurMixedDiagonalEntry s, (d p)^2)/2) =
      ∏ i : Fin m, Real.exp (-(∑ ab : Fin (s i) × Fin (s i),
        (realSchurMixedDiagonalProductEquiv s d i ab)^2)/2) := by
  rw [realSchurMixedDiagonal_energy_sum,← Real.exp_sum]
  congr 1
  rw [← Finset.sum_div,Finset.sum_neg_distrib]

theorem realSchurMixedDiagonalProductEquiv_nativeBlock
    {m : ℕ} (s : Fin m → ℕ) (d : RealSchurMixedDiagonalEntry s → ℝ)
    (u : RealSchurMixedStrictUpperEntry s → ℝ) (i : Fin m) :
    realSchurMixedDiagonalMatrix s (realSchurMixedUpperEntryJoin s d u) i =
      Matrix.of (realSchurMixedDiagonalProductEquiv s d i).curry := by
  ext a b
  simp [realSchurMixedDiagonalMatrix,realSchurMixedUpperEntryJoin,
    realSchurMixedDiagonalProductEquiv_apply]

/-- Exact integration in the independent native diagonal-block entry
coordinates, before separating their spectral and gap variables. -/
theorem realSchurMixedDiagonalProduct_lintegral
    {m : ℕ} (s : Fin m → ℕ) (f : (RealSchurMixedDiagonalEntry s → ℝ) → ℝ≥0∞) :
    (∫⁻ d, f d) = ∫⁻ D : (i : Fin m) → (Fin (s i) × Fin (s i)) → ℝ,
      f ((realSchurMixedDiagonalProductEquiv s).symm D) :=
  MeasurePreserving.lintegral_map_equiv f (realSchurMixedDiagonalProductEquiv s).symm
    (realSchurMixedDiagonalProductEquiv_measurePreserving s).symm

#print axioms realSchurMixedDiagonal_energy_sum
#print axioms realSchurMixedDiagonal_gaussian_product
#print axioms realSchurMixedDiagonalProductEquiv_nativeBlock
#print axioms realSchurMixedDiagonalProduct_lintegral
end SpectralRadiusUpperTail
