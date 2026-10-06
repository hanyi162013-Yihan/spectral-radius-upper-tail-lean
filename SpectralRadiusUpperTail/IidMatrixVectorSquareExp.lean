import SpectralRadiusUpperTail.UniformRowSquareExp

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators ENNReal

lemma iid_matrix_vector_squareExp (μ : Measure ℂ) [IsProbabilityMeasure μ]
    (n : ℕ) (v : Fin n → ℂ) (hv : ∑ j, ‖v j‖^2 ≤ 1)
    (hXi : Integrable (fun x : ℂ => x) μ) (hm : (∫ x : ℂ, x ∂μ) = 0)
    (τ : ℝ) (hτ : 0 < τ) (hexp : Integrable (fun x : ℂ => Real.exp (τ*‖x‖^2)) μ) :
    let c := rowSquareExpExponent τ (∫ x : ℂ, Real.exp (τ*‖x‖^2) ∂μ)
    (∫⁻ x : Fin n → Fin n → ℂ,
      ENNReal.ofReal (Real.exp (c*∑ i, ‖∑ j, v j*x i j‖^2))
      ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))) ≤ ENNReal.ofReal (2^n) := by
  obtain ⟨hc, hi, hb⟩ := iid_row_squareExp μ v hXi hm hv τ hτ hexp
  let c := rowSquareExpExponent τ (∫ x : ℂ, Real.exp (τ*‖x‖^2) ∂μ)
  let f : (Fin n → ℂ) → ℝ := fun y => Real.exp (c*‖∑ j, v j*y j‖^2)
  have hi' : Integrable f (Measure.pi (fun _ : Fin n => μ)) := hi
  have he (x : Fin n → Fin n → ℂ) :
      Real.exp (c*∑ i, ‖∑ j, v j*x i j‖^2) = ∏ i, f (x i) := by
    rw [Finset.mul_sum, Real.exp_sum]
  have hp : Integrable (fun x : Fin n → Fin n → ℂ => ∏ i, f (x i))
      (Measure.pi (fun _ => Measure.pi (fun _ => μ))) := Integrable.fintype_prod (fun _ => hi')
  change (∫⁻ x : Fin n → Fin n → ℂ, ENNReal.ofReal
    (Real.exp (c*∑ i, ‖∑ j, v j*x i j‖^2))
    ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))) ≤ ENNReal.ofReal (2^n)
  simp_rw [he]
  rw [← ofReal_integral_eq_lintegral_ofReal hp (Filter.Eventually.of_forall (fun x => by
    exact Finset.prod_nonneg (fun i _ => Real.exp_nonneg _)))]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_fintype_prod_eq_prod (fun _ y => f y)]
  calc
    _ ≤ ∏ _i : Fin n, (2 : ℝ) := Finset.prod_le_prod
      (fun i _ => integral_nonneg (fun _ => Real.exp_nonneg _)) (fun i _ => hb)
    _ = _ := by simp

#print axioms iid_matrix_vector_squareExp
end SpectralRadiusUpperTail
