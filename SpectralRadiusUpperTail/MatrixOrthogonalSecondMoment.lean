import SpectralRadiusUpperTail.FiniteOrthogonalSecondMoment
import SpectralRadiusUpperTail.GaussianMatrixSandwich

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

/-- Entrywise orthogonality gives exact additivity of expected squared
Hilbert--Schmidt norms. Independence of the matrix summands is not required. -/
theorem matrix_orthogonal_second_moment {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] {a b : ℕ} (μ : Measure Ω)
    (F : ι → Ω → Matrix (Fin a) (Fin b) ℝ)
    (hi : ∀ i j r s, Integrable (fun x => F i x r s * F j x r s) μ)
    (ho : ∀ i j, i ≠ j → ∀ r s, (∫ x, F i x r s * F j x r s ∂μ) = 0) :
    Integrable (fun x => ‖∑ i, F i x‖^2) μ ∧
    (∫ x, ‖∑ i, F i x‖^2 ∂μ) = ∑ i, ∫ x, ‖F i x‖^2 ∂μ := by
  classical
  have hentry (r : Fin a) (s : Fin b) := finite_orthogonal_second_moment μ
    (fun i x => F i x r s) (fun i j => hi i j r s)
    (fun i j h => ho i j h r s)
  have hs (i : ι) (r : Fin a) (s : Fin b) :
      Integrable (fun x => (F i x r s)^2) μ := by
    simpa only [pow_two] using hi i i r s
  have hsum (r : Fin a) : Integrable (fun x => ∑ s, (∑ i, F i x r s)^2) μ :=
    integrable_finsetSum _ (fun s _ => (hentry r s).1)
  constructor
  · simp_rw [real_rectangular_frobenius_norm_sq, Matrix.sum_apply]
    exact integrable_finsetSum _ (fun r _ => hsum r)
  · simp_rw [real_rectangular_frobenius_norm_sq, Matrix.sum_apply]
    rw [integral_finsetSum _ (fun r _ => hsum r)]
    simp_rw [integral_finsetSum _ (fun s _ => (hentry _ s).1)]
    simp_rw [(hentry _ _).2]
    calc
      _ = ∑ r, ∑ i, ∑ s, ∫ x, (F i x r s)^2 ∂μ := by
        apply Finset.sum_congr rfl
        intro r _
        exact Finset.sum_comm
      _ = ∑ i, ∑ r, ∑ s, ∫ x, (F i x r s)^2 ∂μ := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ (fun s _ => hs i r s))]
        simp_rw [integral_finsetSum _ (fun s _ => hs i _ s)]

#print axioms matrix_orthogonal_second_moment
end SpectralRadiusUpperTail
