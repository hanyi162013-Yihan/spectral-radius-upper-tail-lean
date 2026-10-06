import SpectralRadiusUpperTail.ComplexHaarFlatMass
import SpectralRadiusUpperTail.PowerMassLogLower
import SpectralRadiusUpperTail.PositiveEnergyTruncation

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Filter Metric WithLp
open scoped Topology

lemma complex_haar_flat_cost (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ᶠ n : ℕ in atTop,
      0 < (haarSphereProbability (volume : Measure (EuclideanSpace ℂ (Fin n)))).real
        {v | ∀ i : Fin n, ‖v.val i‖ ≤ L/Real.sqrt (n : ℝ)} ∧
      -ε ≤ Real.log ((haarSphereProbability (volume : Measure (EuclideanSpace ℂ (Fin n)))).real
        {v | ∀ i : Fin n, ‖v.val i‖ ≤ L/Real.sqrt (n : ℝ)})/(n : ℝ) := by
  have hi : Integrable (fun x : ℂ => ‖x‖^2) (stdGaussian ℂ) :=
    IsGaussian.memLp_two_id.integrable_norm_pow (by norm_num)
  have hv : (1/2 : ℝ) < ∫ x : ℂ, ‖x‖^2 ∂stdGaussian ℂ := by
    rw [stdGaussian_complex_energy_pseudo.1]
    norm_num
  obtain ⟨k,hk,hk1⟩ := ((positive_energy_truncations_eventually (stdGaussian ℂ) hi hv (ε/2) (by positivity)).and
    (eventually_ge_atTop (1 : ℕ))).exists
  have hkpos : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hq : 0 < (stdGaussian ℂ).real (closedBall (0 : ℂ) (k : ℝ)) :=
    ENNReal.toReal_pos hk.1 (measure_ne_top _ _)
  have hm := complex_haar_flat_mass_lower (k : ℝ) hkpos hk.1 hk.2.1
  have hl := eventual_log_lower_of_power_lower _ _ hq hm (ε/2) (by positivity)
  refine ⟨2*(k : ℝ),?_,?_⟩
  · have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    linarith
  · filter_upwards [hl,hm] with n hn hnm
    constructor
    · exact lt_of_lt_of_le (by positivity) hnm
    · linarith [hk.2.2]

#print axioms complex_haar_flat_cost
end SpectralRadiusUpperTail
