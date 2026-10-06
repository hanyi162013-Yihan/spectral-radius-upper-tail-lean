import SpectralRadiusUpperTail.IidSimpleWordVariance
import SpectralRadiusUpperTail.FiniteOrthogonalSecondMoment
import SpectralRadiusUpperTail.SchurOffDiagonalMoment

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

lemma gaussian_coordinate_cross_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) :
    (∫ x : ι → ℝ, x i*x j ∂Measure.pi (fun _ => standardNormal)) = 0 := by
  have hm : (∫ z : ℝ, z ∂standardNormal) = 0 := by
    simpa using standardNormal_odd_moment 0
  have h := iidWordPair_singleton_zero standardNormal hm
    (fun _ : Fin 1 => i) (fun _ : Fin 1 => j) i (by
      simp [entryMultiplicity, hij.symm])
  simpa using h

/-- The exact Gaussian coordinate isometry, with integrability proved
before taking the integral. -/
theorem gaussian_linear_form_second_moment {ι : Type*} [Fintype ι]
    (c : ι → ℝ) :
    Integrable (fun x : ι → ℝ => (∑ i, c i*x i)^2)
      (Measure.pi (fun _ => standardNormal)) ∧
    (∫ x : ι → ℝ, (∑ i, c i*x i)^2 ∂Measure.pi (fun _ => standardNormal)) =
      ∑ i, (c i)^2 := by
  classical
  have hi (i j : ι) : Integrable (fun x : ι → ℝ => (c i*x i)*(c j*x j))
      (Measure.pi (fun _ => standardNormal)) := by
    have h := (iid_real_word_pair_integrable standardNormal standardNormal_pow_integrable
      (fun _ : Fin 1 => i) (fun _ : Fin 1 => j)).const_mul (c i*c j)
    simp only [Fintype.prod_unique, Fin.default_eq_zero] at h
    convert h using 1
    funext x
    ring
  have ho (i j : ι) (hij : i ≠ j) :
      (∫ x : ι → ℝ, (c i*x i)*(c j*x j) ∂Measure.pi (fun _ => standardNormal)) = 0 := by
    have he (x : ι → ℝ) : (c i*x i)*(c j*x j) = (c i*c j)*(x i*x j) := by ring
    simp_rw [he]
    rw [integral_const_mul, gaussian_coordinate_cross_zero i j hij, mul_zero]
  obtain ⟨hint, heq⟩ := finite_orthogonal_second_moment
    (Measure.pi (fun _ : ι => standardNormal)) (fun i x => c i*x i) hi ho
  refine ⟨hint, heq.trans ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_pow]
  rw [integral_const_mul, gaussian_coordinate_square_integral, mul_one]

#print axioms gaussian_coordinate_cross_zero
#print axioms gaussian_linear_form_second_moment
end SpectralRadiusUpperTail
