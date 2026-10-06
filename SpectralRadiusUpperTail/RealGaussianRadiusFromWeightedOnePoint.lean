import SpectralRadiusUpperTail.RealGaussianWeightedRadiusConditional
import SpectralRadiusUpperTail.MomentExponentTransfer
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped Topology

/-- The scalar clipped spectral-radius moment itself gives the needed Markov
comparison; no Schur decomposition or Hilbert--Schmidt power is involved. -/
theorem realGaussianRadius_markov_of_clippedPower
    (n k : ℕ) (hn : 0 < n)
    (hroot : Integrable (realGaussianExteriorRootPower n k)
      (gaussianMatrixLaw n))
    (r : ℝ) (hr : 0 < r) :
    (gaussianMatrixLaw n).real
      {x | r ≤ realMatrixRadius
        ((1/Real.sqrt (n : ℝ)) • entryMatrix x)} ≤
      (∫ x, realGaussianClippedRadiusPower n k x
        ∂gaussianMatrixLaw n)/r^(2*k) := by
  let M := gaussianMatrixLaw n
  let f := realGaussianClippedRadiusPower n k
  have hf : Integrable f M :=
    realGaussianClippedRadiusPower_integrable n k hn hroot
  have hnonneg : 0 ≤ᵐ[M] f := Eventually.of_forall (fun x => by
    dsimp [f, realGaussianClippedRadiusPower]
    positivity)
  have hpowpos : 0 < r^(2*k) := pow_pos hr _
  have hsub : {x | r ≤ realMatrixRadius
      ((1/Real.sqrt (n : ℝ)) • entryMatrix x)} ⊆
      {x | r^(2*k) ≤ f x} := by
    intro x hx
    change r ≤ realMatrixRadius
      ((1/Real.sqrt (n : ℝ)) • entryMatrix x) at hx
    dsimp [f, realGaussianClippedRadiusPower]
    exact pow_le_pow_left₀ hr.le (hx.trans (le_max_right _ _)) _
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg hf (r^(2*k))
  have hm : M.real {x | r ≤ realMatrixRadius
      ((1/Real.sqrt (n : ℝ)) • entryMatrix x)} ≤
      M.real {x | r^(2*k) ≤ f x} := measureReal_mono hsub
  exact hm.trans ((le_div_iff₀ hpowpos).2 (by simpa [mul_comm] using hmarkov))

/-- The real-Ginibre weighted one-point bound alone gives the Gaussian
spectral-radius large-deviation upper bound. This route does not use the
conditional Schur law needed for Hilbert--Schmidt matrix powers. -/
theorem realGaussianRadius_upper_of_weightedOnePoint
    (hroot : ∀ n k, 3 ≤ n →
      Integrable (realGaussianExteriorRootPower n k)
        (gaussianMatrixLaw n))
    (hidentity : ∀ n k, 3 ≤ n →
      (∫ x, realGaussianExteriorRootPower n k x
        ∂gaussianMatrixLaw n) ≤
          realGinibreWeightedOnePointEnvelope n k)
    (r : ℝ) (hr : 1 < r) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (gaussianMatrixLaw n).real
        {x | r ≤ realMatrixRadius
          ((1/Real.sqrt (n : ℝ)) • entryMatrix x)} ≤
        Real.exp ((n : ℝ)*(-rate 1 r+ε)) := by
  apply sharp_tail_of_power_moments
    (fun n => (gaussianMatrixLaw n).real
      {x | r ≤ realMatrixRadius
        ((1/Real.sqrt (n : ℝ)) • entryMatrix x)})
    (fun n k => ∫ x, realGaussianClippedRadiusPower n k x
      ∂gaussianMatrixLaw n) 1 r (by norm_num) hr ?_ ?_ ε hε
  · intro α hα
    filter_upwards [eventually_ge_atTop 3] with n hn
    exact realGaussianRadius_markov_of_clippedPower n _ (by omega)
      (hroot n _ hn) r (by linarith)
  · intro α hα δ hδ
    exact realGaussianClippedRadiusPower_upper_of_onePoint
      hroot hidentity (fun n => ⌊α*(n : ℝ)⌋₊) α hα
      (floor_linear_power_ratio α hα) δ hδ

#print axioms realGaussianRadius_markov_of_clippedPower
#print axioms realGaussianRadius_upper_of_weightedOnePoint
end SpectralRadiusUpperTail
