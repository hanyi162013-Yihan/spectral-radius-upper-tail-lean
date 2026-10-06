import SpectralRadiusUpperTail.GaussianHaarDirection
import SpectralRadiusUpperTail.NormalizeFlatVector
import SpectralRadiusUpperTail.TruncatedProductGoodEvent

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Filter Metric WithLp
open scoped Topology BigOperators ENNReal

lemma real_haar_flat_mass_lower (K : ℝ) (hK : 0 ≤ K)
    (hmass : standardNormal (closedBall (0 : ℝ) K) ≠ 0)
    (hmean : (1/2 : ℝ) < ∫ x : ℝ, ‖x‖^2 ∂standardNormal[|closedBall (0 : ℝ) K]) :
    ∀ᶠ n : ℕ in atTop,
      (standardNormal.real (closedBall (0 : ℝ) K))^n/2 ≤
        (haarSphereProbability (volume : Measure (EuclideanSpace ℝ (Fin n)))).real
          {v | ∀ i : Fin n, ‖v.val i‖ ≤ (2*K)/Real.sqrt (n : ℝ)} := by
  have ht := original_truncated_good_event_lower standardNormal K hK hmass hmean
  filter_upwards [ht,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : 0 < n := by omega
  let F : Set (EuclideanSpace ℝ (Fin n)) := {v | ∀ i : Fin n, ‖v i‖ ≤ (2*K)/Real.sqrt (n : ℝ)}
  have hF : MeasurableSet F := by
    simp only [F,Set.setOf_forall]
    apply MeasurableSet.iInter
    intro i
    apply measurableSet_le _ measurable_const
    fun_prop
  have he := congrArg (fun ρ : Measure (EuclideanSpace ℝ (Fin n)) => ρ.real F)
    (standardNormal_direction_eq_haarSphere n hnpos)
  rw [map_measureReal_apply (by fun_prop) hF,map_measureReal_apply measurable_subtype_coe hF] at he
  change (standardNormal.real (closedBall (0 : ℝ) K))^n/2 ≤
    (haarSphereProbability (volume : Measure (EuclideanSpace ℝ (Fin n)))).real (Subtype.val ⁻¹' F)
  rw [← he]
  apply hn.trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  have henergy : (n : ℝ)/4 ≤ ‖toLp 2 x‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact hx.2.le
  have hcoord : ∀ i : Fin n, ‖(toLp 2 x : EuclideanSpace ℝ (Fin n)) i‖ ≤ K := by
    intro i
    have hh := hx.1 i (Set.mem_univ i)
    simpa only [mem_closedBall,dist_zero_right] using hh
  exact normalize_coordinate_flat_bound (toLp 2 x) hnpos K hK henergy hcoord

#print axioms real_haar_flat_mass_lower
end SpectralRadiusUpperTail
