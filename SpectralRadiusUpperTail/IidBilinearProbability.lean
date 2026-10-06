import SpectralRadiusUpperTail.IidBilinearMoment
import SpectralRadiusUpperTail.SecondMomentProbability

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped BigOperators Topology
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂] {N : ℕ}

/-- Actual iid bilinear tail bound for deterministic vectors with energy at most one. -/
lemma iidBilinear_probability_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (p q : Fin N → 𝕂) (hX : MemLp (fun x : 𝕂 => x) 2 μ)
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hv : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (hp : ∑ i, ‖p i‖^2 ≤ 1) (hq : ∑ j, ‖q j‖^2 ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    (Measure.pi (fun _ : Fin N × Fin N => μ)).real {x | ε ≤ ‖iidBilinear p q x‖} ≤
      (1/(N : ℝ))/ε^2 := by
  have hmem := iidBilinear_memLp μ p q hX
  have hi := (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
  have hb := norm_probability_le_secondMoment _ (iidBilinear p q) hi ε hε
  rw [iidBilinear_secondMoment μ p q hX hm hv] at hb
  have hq0 : 0 ≤ ∑ j, ‖q j‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he : (∑ i, ‖p i‖^2)*(∑ j, ‖q j‖^2) ≤ 1 := by nlinarith
  have hn : 0 ≤ 1/(N : ℝ) := by positivity
  have hh := mul_le_mul_of_nonneg_left he hn
  apply hb.trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg ε)
  nlinarith

/-- The first iid matrix power has vanishing deterministic bilinear coefficients. -/
lemma iidBilinear_probability_tendsto (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (p q : (n : ℕ) → Fin n → 𝕂) (hX : MemLp (fun x : 𝕂 => x) 2 μ)
    (hm : (∫ x : 𝕂, x ∂μ) = 0) (hv : (∫ x : 𝕂, ‖x‖^2 ∂μ) = 1)
    (hp : ∀ n, ∑ i, ‖p n i‖^2 ≤ 1) (hq : ∀ n, ∑ j, ‖q n j‖^2 ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (Measure.pi (fun _ : Fin n × Fin n => μ)).real
      {x | ε ≤ ‖iidBilinear (p n) (q n) x‖}) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => iidBilinear_probability_le μ (p n) (q n) hX hm hv (hp n) (hq n) ε hε)
  have hh : Tendsto (fun n : ℕ => 1/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa only [zero_div] using hh.div_const (ε^2)

#print axioms iidBilinear_probability_le
#print axioms iidBilinear_probability_tendsto
end SpectralRadiusUpperTail
