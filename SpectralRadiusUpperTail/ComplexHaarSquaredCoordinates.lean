import SpectralRadiusUpperTail.ComplexGaussianNormSquare
import SpectralRadiusUpperTail.ComplexHaarDirection

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory WithLp Metric
open scoped BigOperators

lemma complex_normalized_coordinate_square (n : ℕ) (x : Fin n → ℂ) (i : Fin n) :
    ‖(‖toLp 2 x‖⁻¹ • toLp 2 x : EuclideanSpace ℂ (Fin n)) i‖^2 =
      ‖x i‖^2/(∑ j, ‖x j‖^2) := by
  simp only [PiLp.smul_apply,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,mul_pow,inv_pow,
    EuclideanSpace.norm_sq_eq,div_eq_mul_inv]
  ring

/-- Haar squared coordinates are normalized independent exponential variables. -/
lemma complex_haar_squared_coordinates (n : ℕ) (hn : 0 < n) :
    (haarSphereProbability (volume : Measure (EuclideanSpace ℂ (Fin n)))).map
      (fun v : sphere (0 : EuclideanSpace ℂ (Fin n)) 1 => fun i => ‖v.val i‖^2) =
    (Measure.pi (fun _ : Fin n => expMeasure (1/2))).map
      (fun y : Fin n → ℝ => fun i => y i/(∑ j, y j)) := by
  have hs : Measurable (fun v : EuclideanSpace ℂ (Fin n) => fun i => ‖v i‖^2) := by fun_prop
  have hg : Measurable (fun x : Fin n → ℂ => ‖toLp 2 x‖⁻¹ • toLp 2 x) := by fun_prop
  have he := congrArg (fun ρ : Measure (EuclideanSpace ℂ (Fin n)) =>
    ρ.map (fun v => fun i => ‖v i‖^2)) (complex_gaussian_direction_eq_haarSphere n hn)
  rw [Measure.map_map hs hg,Measure.map_map hs measurable_subtype_coe] at he
  have heq : (fun x : Fin n → ℂ => (fun v : EuclideanSpace ℂ (Fin n) => fun i => ‖v i‖^2)
      (‖toLp 2 x‖⁻¹ • toLp 2 x)) =
      (fun x : Fin n → ℂ => (fun y : Fin n → ℝ => fun i => y i/(∑ j, y j))
        (fun j => ‖x j‖^2)) := by
    funext x i
    exact complex_normalized_coordinate_square n x i
  simp only [Function.comp_def] at he
  rw [heq] at he
  have hmap := Measure.map_map (μ := Measure.pi (fun _ : Fin n => stdGaussian ℂ))
    (show Measurable (fun y : Fin n → ℝ => fun i => y i/(∑ j, y j)) by fun_prop)
    (show Measurable (fun x : Fin n → ℂ => fun j => ‖x j‖^2) by fun_prop)
  simp only [Function.comp_def] at hmap
  rw [← hmap,stdComplexGaussian_pi_normSquare_exponential] at he
  exact he.symm

#print axioms complex_normalized_coordinate_square
#print axioms complex_haar_squared_coordinates
end SpectralRadiusUpperTail
