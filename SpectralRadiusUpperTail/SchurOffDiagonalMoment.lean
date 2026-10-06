import SpectralRadiusUpperTail.GaussianMoments
import Mathlib.MeasureTheory.Integral.Pi

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

lemma gaussian_coordinate_square_integrable {ι : Type*} [Fintype ι] (i : ι) :
    Integrable (fun x : ι → ℝ => (x i)^2) (Measure.pi (fun _ : ι => standardNormal)) :=
  (measurePreserving_eval (fun _ : ι => standardNormal) i).integrable_comp_of_integrable
    (standardNormal_pow_integrable 2)

lemma gaussian_coordinate_square_integral {ι : Type*} [Fintype ι] (i : ι) :
    (∫ x : ι → ℝ, (x i)^2 ∂Measure.pi (fun _ : ι => standardNormal)) = 1 := by
  have hm := (measurePreserving_eval (fun _ : ι => standardNormal) i).map_eq
  calc
    _ = ∫ z : ℝ, z^2 ∂(Measure.pi (fun _ : ι => standardNormal)).map (Function.eval i) :=
      (integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)).symm
    _ = 1 := by rw [hm]; exact standardNormal_second_moment

/-- Actual rectangular Gaussian block with entries N(0,1/n): its squared
Hilbert--Schmidt expectation is the number of entries divided by n. -/
lemma gaussian_offdiagonal_block_second_moment (a b n : ℕ) (hn : 0 < n) :
    (∫ x : Fin a × Fin b → ℝ, ∑ ij, (x ij/Real.sqrt n)^2
      ∂Measure.pi (fun _ : Fin a × Fin b => standardNormal)) = (a : ℝ)*b/n := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hi (ij : Fin a × Fin b) : Integrable (fun x : Fin a × Fin b → ℝ => (x ij/Real.sqrt n)^2)
      (Measure.pi (fun _ => standardNormal)) := by
    simp_rw [div_pow]
    exact (gaussian_coordinate_square_integrable ij).div_const _
  rw [integral_finsetSum _ (fun ij _ => hi ij)]
  simp_rw [div_pow, integral_div, gaussian_coordinate_square_integral,
    Real.sq_sqrt hnR.le]
  simp [Nat.cast_mul, div_eq_mul_inv, mul_assoc]

lemma gaussian_schur_offdiagonal_budget (a b n : ℕ) (hn : 0 < n)
    (ha : a ≤ 2) (hb : b ≤ 2) :
    (∫ x : Fin a × Fin b → ℝ, ∑ ij, (x ij/Real.sqrt n)^2
      ∂Measure.pi (fun _ : Fin a × Fin b => standardNormal)) ≤ 4/(n : ℝ) := by
  rw [gaussian_offdiagonal_block_second_moment a b n hn]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  have hab : a*b ≤ 4 := by nlinarith
  exact_mod_cast hab

#print axioms gaussian_offdiagonal_block_second_moment
#print axioms gaussian_schur_offdiagonal_budget
end SpectralRadiusUpperTail
