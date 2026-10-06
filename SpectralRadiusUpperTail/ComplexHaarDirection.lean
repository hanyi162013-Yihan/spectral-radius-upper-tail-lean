import SpectralRadiusUpperTail.ComplexGaussianProductLaw
import SpectralRadiusUpperTail.StandardGaussianRadialDensity

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory WithLp

lemma complex_gaussian_direction_eq_haarSphere (n : ℕ) (hn : 0 < n) :
    (Measure.pi (fun _ : Fin n => stdGaussian ℂ)).map
      (fun x => ‖toLp 2 x‖⁻¹ • toLp 2 x) =
      (haarSphereProbability (volume : Measure (EuclideanSpace ℂ (Fin n)))).map Subtype.val := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hh := congrArg (fun ρ : Measure (EuclideanSpace ℂ (Fin n)) =>
    ρ.map (fun x => ‖x‖⁻¹ • x)) (complex_stdGaussian_product_law n)
  rw [Measure.map_map (by fun_prop) (by fun_prop),stdGaussian_direction_eq_haarSphere] at hh
  exact hh

#print axioms complex_gaussian_direction_eq_haarSphere
end SpectralRadiusUpperTail
