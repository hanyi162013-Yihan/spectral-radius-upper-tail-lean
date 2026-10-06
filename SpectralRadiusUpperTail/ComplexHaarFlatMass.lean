import SpectralRadiusUpperTail.ComplexHaarDirection
import SpectralRadiusUpperTail.NormalizeFlatVector
import SpectralRadiusUpperTail.TruncatedProductGoodEvent

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory Filter Metric WithLp
open scoped Topology BigOperators ENNReal

lemma complex_haar_flat_mass_lower (K : ℝ) (hK : 0 ≤ K)
    (hmass : (stdGaussian ℂ) (closedBall (0 : ℂ) K) ≠ 0)
    (hmean : (1/2 : ℝ) < ∫ x : ℂ, ‖x‖^2 ∂(stdGaussian ℂ)[|closedBall (0 : ℂ) K]) :
    ∀ᶠ n : ℕ in atTop,
      ((stdGaussian ℂ).real (closedBall (0 : ℂ) K))^n/2 ≤
        (haarSphereProbability (volume : Measure (EuclideanSpace ℂ (Fin n)))).real
          {v | ∀ i : Fin n, ‖v.val i‖ ≤ (2*K)/Real.sqrt (n : ℝ)} := by
  have ht := original_truncated_good_event_lower (stdGaussian ℂ) K hK hmass hmean
  filter_upwards [ht,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : 0 < n := by omega
  let F : Set (EuclideanSpace ℂ (Fin n)) := {v | ∀ i : Fin n, ‖v i‖ ≤ (2*K)/Real.sqrt (n : ℝ)}
  have hF : MeasurableSet F := by
    simp only [F,Set.setOf_forall]
    apply MeasurableSet.iInter
    intro i
    apply measurableSet_le _ measurable_const
    fun_prop
  have he := congrArg (fun ρ : Measure (EuclideanSpace ℂ (Fin n)) => ρ.real F)
    (complex_gaussian_direction_eq_haarSphere n hnpos)
  rw [map_measureReal_apply (by fun_prop) hF,map_measureReal_apply measurable_subtype_coe hF] at he
  change ((stdGaussian ℂ).real (closedBall (0 : ℂ) K))^n/2 ≤
    (haarSphereProbability (volume : Measure (EuclideanSpace ℂ (Fin n)))).real (Subtype.val ⁻¹' F)
  rw [← he]
  apply hn.trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  have henergy : (n : ℝ)/4 ≤ ‖toLp 2 x‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact hx.2.le
  have hcoord : ∀ i : Fin n, ‖(toLp 2 x : EuclideanSpace ℂ (Fin n)) i‖ ≤ K := by
    intro i
    have hh := hx.1 i (Set.mem_univ i)
    simpa only [mem_closedBall,dist_zero_right] using hh
  exact normalize_coordinate_flat_bound (toLp 2 x) hnpos K hK henergy hcoord

#print axioms complex_haar_flat_mass_lower
end SpectralRadiusUpperTail
