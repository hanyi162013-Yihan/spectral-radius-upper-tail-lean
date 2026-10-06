import SpectralRadiusUpperTail.RealPairGaussianGapDisintegration
import SpectralRadiusUpperTail.SchurGapBlock

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Frobenius

theorem realPairGapBlockEntries_eq_gapBlock (x u s : ℝ) (hu : 0 ≤ u) (hs : 0 ≤ s) :
    Matrix.of (realPairGapBlockEntries x (u,s)).curry =
      realSchurBlock x (schurGapUpper (Real.sqrt u) s) (schurGapLower (Real.sqrt u) s) := by
  unfold realPairGapBlockEntries realSchurPairFromCoordinates schurGapUpper schurGapLower
  rw [max_eq_right hs,Real.sq_sqrt hu]
  rfl

/-- The canonical blocks produced by the actual Gaussian change of
variables satisfy the already checked conditional block-power bound. -/
theorem realPairGapBlock_power_expectation
    (n x u ε : ℝ) (hn : 0 < n) (hu : 0 < u) (hε : 0 < ε) (k : ℕ) :
    Integrable (fun s : ℝ => ‖(Matrix.of (realPairGapBlockEntries x (u,s)).curry)^k‖^2)
      (schurSquaredGapLaw n (Real.sqrt u)) ∧
    (∫ s : ℝ, ‖(Matrix.of (realPairGapBlockEntries x (u,s)).curry)^k‖^2
      ∂schurSquaredGapLaw n (Real.sqrt u)) ≤
        (2+2/(n*ε^2))*(‖(x : ℂ)+(Real.sqrt u)*Complex.I‖+ε)^(2*k) := by
  have h := schurGapBlock_power_expectation n x (Real.sqrt u) ε hn
    (Real.sqrt_pos.mpr hu) hε k
  have he : (fun s : ℝ => ‖(Matrix.of (realPairGapBlockEntries x (u,s)).curry)^k‖^2) =ᵐ[
      schurSquaredGapLaw n (Real.sqrt u)]
      (fun s => ‖(realSchurBlock x (schurGapUpper (Real.sqrt u) s)
        (schurGapLower (Real.sqrt u) s))^k‖^2) := by
    filter_upwards [schurSquaredGapLaw_nonnegative n (Real.sqrt u) hn] with s hs
    rw [realPairGapBlockEntries_eq_gapBlock x u s hu.le hs]
  exact ⟨h.1.congr he.symm,(integral_congr_ae he).trans_le h.2⟩

theorem realPairGapBlock_power_lintegral_bound
    (n x u ε : ℝ) (hn : 0 < n) (hu : 0 < u) (hε : 0 < ε) (k : ℕ) :
    (∫⁻ s : ℝ, ENNReal.ofReal (‖(Matrix.of (realPairGapBlockEntries x (u,s)).curry)^k‖^2)
      ∂schurSquaredGapLaw n (Real.sqrt u)) ≤
        ENNReal.ofReal ((2+2/(n*ε^2))*(‖(x : ℂ)+(Real.sqrt u)*Complex.I‖+ε)^(2*k)) := by
  have h := realPairGapBlock_power_expectation n x u ε hn hu hε k
  rw [← ofReal_integral_eq_lintegral_ofReal h.1
    (Filter.Eventually.of_forall (fun s => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal h.2

#print axioms realPairGapBlockEntries_eq_gapBlock
#print axioms realPairGapBlock_power_expectation
#print axioms realPairGapBlock_power_lintegral_bound
end SpectralRadiusUpperTail
