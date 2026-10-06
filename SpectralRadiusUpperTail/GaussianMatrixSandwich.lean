import SpectralRadiusUpperTail.GaussianCoordinateIsometry
import SpectralRadiusUpperTail.SpectralWitness

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma real_rectangular_frobenius_norm_sq {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ) :
    ‖A‖^2 = ∑ i, ∑ j, (A i j)^2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
  · simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      Real.rpow_nonneg (norm_nonneg _) _))

def gaussianEntryBlock {b c : ℕ} (x : Fin b × Fin c → ℝ) : Matrix (Fin b) (Fin c) ℝ :=
  fun i j => x (i,j)

lemma gaussian_sandwich_entry {a b c d : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (B : Matrix (Fin c) (Fin d) ℝ)
    (x : Fin b × Fin c → ℝ) (i : Fin a) (j : Fin d) :
    (A*gaussianEntryBlock x*B) i j =
      ∑ uv : Fin b × Fin c, (A i uv.1*B uv.2 j)*x uv := by
  simp only [Matrix.mul_apply, gaussianEntryBlock, Finset.sum_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- Exact Gaussian contraction for a rectangular matrix between two
fixed matrices. This is stronger than multiplying Frobenius norm bounds. -/
theorem gaussian_matrix_sandwich_second_moment {a b c d : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (B : Matrix (Fin c) (Fin d) ℝ) :
    Integrable (fun x : Fin b × Fin c → ℝ => ‖A*gaussianEntryBlock x*B‖^2)
      (Measure.pi (fun _ => standardNormal)) ∧
    (∫ x : Fin b × Fin c → ℝ, ‖A*gaussianEntryBlock x*B‖^2
      ∂Measure.pi (fun _ => standardNormal)) = ‖A‖^2*‖B‖^2 := by
  have he (i : Fin a) (j : Fin d) := gaussian_linear_form_second_moment
    (fun uv : Fin b × Fin c => A i uv.1*B uv.2 j)
  have hi (i : Fin a) (j : Fin d) :
      Integrable (fun x : Fin b × Fin c → ℝ => ((A*gaussianEntryBlock x*B) i j)^2)
        (Measure.pi (fun _ => standardNormal)) := by
    simpa only [gaussian_sandwich_entry] using (he i j).1
  have hmoment (i : Fin a) (j : Fin d) :
      (∫ x : Fin b × Fin c → ℝ, ((A*gaussianEntryBlock x*B) i j)^2
        ∂Measure.pi (fun _ => standardNormal)) =
          (∑ u, (A i u)^2)*(∑ v, (B v j)^2) := by
    simp_rw [gaussian_sandwich_entry]
    rw [(he i j).2]
    simp only [Fintype.sum_prod_type, mul_pow, Finset.sum_mul_sum]
  constructor
  · simp_rw [real_rectangular_frobenius_norm_sq]
    exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))
  · simp_rw [real_rectangular_frobenius_norm_sq]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
    simp_rw [integral_finsetSum _ (fun j _ => hi _ j), hmoment]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    rw [Finset.sum_comm (f := fun j v => (B v j)^2)]

#print axioms gaussian_matrix_sandwich_second_moment
end SpectralRadiusUpperTail
