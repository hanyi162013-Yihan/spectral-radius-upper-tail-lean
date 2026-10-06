import SpectralRadiusUpperTail.PositiveSphereNormWitness
import SpectralRadiusUpperTail.IidMatrixVectorSquareExp
import SpectralRadiusUpperTail.MatrixVectorEnergyRows
import SpectralRadiusUpperTail.HaarSphereDirection
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace SpectralRadiusUpperTail
open MeasureTheory Metric
open scoped ENNReal BigOperators

lemma positive_sphere_moment_measurable (n : ℕ) (hn : 0 < n) (a : ℝ) :
    Measurable (fun x : Fin n → Fin n → ℂ => complexSpherePositiveMoment n a (Matrix.of x)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  letI := haarSphereProbability_probability (volume : Measure (EuclideanSpace ℂ (Fin n)))
  have hm : Measurable (fun p : (sphere (0 : EuclideanSpace ℂ (Fin n)) 1) ×
      (Fin n → Fin n → ℂ) => ENNReal.ofReal (Real.exp (a*∑ i, ‖∑ j, p.1.val j*p.2 i j‖^2))) := by
    fun_prop
  simp_rw [complexSpherePositiveMoment, matrix_vector_energy_rows]
  exact hm.lintegral_prod_left'

lemma iid_positive_sphere_moment (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (hXi : Integrable (fun x : ℂ => x) μ)
    (hm : (∫ x : ℂ, x ∂μ) = 0) (τ : ℝ) (hτ : 0 < τ)
    (hexp : Integrable (fun x : ℂ => Real.exp (τ*‖x‖^2)) μ) :
    let c := rowSquareExpExponent τ (∫ x : ℂ, Real.exp (τ*‖x‖^2) ∂μ)
    (∫⁻ x : Fin n → Fin n → ℂ, complexSpherePositiveMoment n c (Matrix.of x)
      ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))) ≤ ENNReal.ofReal (2^n) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  letI := haarSphereProbability_probability (volume : Measure (EuclideanSpace ℂ (Fin n)))
  let c := rowSquareExpExponent τ (∫ x : ℂ, Real.exp (τ*‖x‖^2) ∂μ)
  let F := fun p : (Fin n → Fin n → ℂ) × (sphere (0 : EuclideanSpace ℂ (Fin n)) 1) =>
    ENNReal.ofReal (Real.exp (c*∑ i, ‖∑ j, p.2.val j*p.1 i j‖^2))
  have hF : Measurable F := by dsimp [F]; fun_prop
  change (∫⁻ x : Fin n → Fin n → ℂ, complexSpherePositiveMoment n c (Matrix.of x)
    ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))) ≤ _
  simp_rw [complexSpherePositiveMoment, matrix_vector_energy_rows]
  rw [lintegral_lintegral_swap hF.aemeasurable]
  calc
    _ ≤ ∫⁻ _v : sphere (0 : EuclideanSpace ℂ (Fin n)) 1, ENNReal.ofReal (2^n)
        ∂haarSphereProbability (volume : Measure (EuclideanSpace ℂ (Fin n))) := by
      apply lintegral_mono
      intro v
      apply iid_matrix_vector_squareExp μ n (fun j => v.val j) ?_ hXi hm τ hτ hexp
      rw [← EuclideanSpace.norm_sq_eq, mem_sphere_zero_iff_norm.mp v.property]
      norm_num
    _ = _ := by simp

#print axioms positive_sphere_moment_measurable
#print axioms iid_positive_sphere_moment
end SpectralRadiusUpperTail
