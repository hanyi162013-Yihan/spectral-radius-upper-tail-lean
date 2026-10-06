import SpectralRadiusUpperTail.RealHaarFlatMass
import SpectralRadiusUpperTail.PowerMassLogLower
import SpectralRadiusUpperTail.GaussianMoments

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Filter Metric WithLp
open scoped Topology

lemma real_haar_flat_cost (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ᶠ n : ℕ in atTop,
      0 < (haarSphereProbability (volume : Measure (EuclideanSpace ℝ (Fin n)))).real
        {v | ∀ i : Fin n, ‖v.val i‖ ≤ L/Real.sqrt (n : ℝ)} ∧
      -ε ≤ Real.log ((haarSphereProbability (volume : Measure (EuclideanSpace ℝ (Fin n)))).real
        {v | ∀ i : Fin n, ‖v.val i‖ ≤ L/Real.sqrt (n : ℝ)})/(n : ℝ) := by
  have hi : Integrable (fun x : ℝ => ‖x‖^2) standardNormal := by
    simpa only [Real.norm_eq_abs,sq_abs] using standardNormal_pow_integrable 2
  have hv : (∫ x : ℝ, ‖x‖^2 ∂standardNormal) = 1 := by
    simpa only [Real.norm_eq_abs,sq_abs] using standardNormal_second_moment
  obtain ⟨k,hk,hk1⟩ := ((good_entry_truncations_eventually standardNormal hi hv (ε/2) (by positivity)).and
    (eventually_ge_atTop (1 : ℕ))).exists
  have hkpos : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hq : 0 < standardNormal.real (closedBall (0 : ℝ) (k : ℝ)) :=
    ENNReal.toReal_pos hk.1 (measure_ne_top _ _)
  have hm := real_haar_flat_mass_lower (k : ℝ) hkpos hk.1 hk.2.1
  have hl := eventual_log_lower_of_power_lower _ _ hq hm (ε/2) (by positivity)
  refine ⟨2*(k : ℝ),?_,?_⟩
  · have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    linarith
  · filter_upwards [hl,hm] with n hn hnm
    constructor
    · exact lt_of_lt_of_le (by positivity) hnm
    · linarith [hk.2.2]

#print axioms real_haar_flat_cost
end SpectralRadiusUpperTail
