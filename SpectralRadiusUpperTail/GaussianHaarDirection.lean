import SpectralRadiusUpperTail.GaussianEuclideanDensity
import SpectralRadiusUpperTail.GaussianWholeDirection

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp
open scoped ENNReal

lemma standardNormal_direction_eq_haarSphere (n : ℕ) (hn : 0 < n) :
    (Measure.pi (fun _ : Fin n => standardNormal)).map
      (fun x => ‖toLp 2 x‖⁻¹ • toLp 2 x) =
      (haarSphereProbability (volume : Measure (EuclideanSpace ℝ (Fin n)))).map Subtype.val := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hh := congrArg (fun ρ : Measure (EuclideanSpace ℝ (Fin n)) =>
    ρ.map (fun x => ‖x‖⁻¹ • x)) (standardNormal_euclidean_eq_normalizedTilt n hn)
  rw [Measure.map_map (by fun_prop) (PiLp.volume_preserving_toLp (Fin n)).measurable,
    gaussian_whole_direction_eq_haarSphere volume (1/2) (by norm_num)] at hh
  exact hh

#print axioms standardNormal_direction_eq_haarSphere
end SpectralRadiusUpperTail
