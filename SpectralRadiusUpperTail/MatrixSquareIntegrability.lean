import SpectralRadiusUpperTail.MatrixOrthogonalSecondMoment

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma real_integrable_mul_of_squares {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hi : Integrable (fun x => (f x)^2) μ) (hj : Integrable (fun x => (g x)^2) μ) :
    Integrable (fun x => f x*g x) μ := by
  apply (hi.add hj).mono' (hf.mul hg).aestronglyMeasurable
  filter_upwards [] with x
  change |f x*g x| ≤ (f x)^2+(g x)^2
  rw [abs_mul]
  nlinarith [sq_nonneg (|f x|-|g x|), sq_abs (f x), sq_abs (g x)]

lemma matrix_entry_sq_le_frobenius {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℝ)
    (r : Fin a) (s : Fin b) : (A r s)^2 ≤ ‖A‖^2 := by
  rw [real_rectangular_frobenius_norm_sq]
  calc
    _ ≤ ∑ j, (A r j)^2 := Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ s)
    _ ≤ ∑ i, ∑ j, (A i j)^2 := Finset.single_le_sum
      (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Finset.mem_univ r)

lemma matrix_entry_pair_integrable {Ω : Type*} [MeasurableSpace Ω] {a b : ℕ}
    (μ : Measure Ω) (F G : Ω → Matrix (Fin a) (Fin b) ℝ)
    (hF : ∀ r s, Measurable (fun x => F x r s))
    (hG : ∀ r s, Measurable (fun x => G x r s))
    (hi : Integrable (fun x => ‖F x‖^2) μ) (hj : Integrable (fun x => ‖G x‖^2) μ)
    (r : Fin a) (s : Fin b) : Integrable (fun x => F x r s*G x r s) μ := by
  have hfi : Integrable (fun x => (F x r s)^2) μ :=
    hi.mono_nonneg ((hF r s).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (Filter.Eventually.of_forall (fun x => matrix_entry_sq_le_frobenius (F x) r s))
  have hgi : Integrable (fun x => (G x r s)^2) μ :=
    hj.mono_nonneg ((hG r s).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))
      (Filter.Eventually.of_forall (fun x => matrix_entry_sq_le_frobenius (G x) r s))
  exact real_integrable_mul_of_squares μ _ _ (hF r s) (hG r s) hfi hgi

/-- Matrix Parseval with the natural square-integrability hypotheses. -/
theorem matrix_orthogonal_second_moment_of_squares {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] {a b : ℕ} (μ : Measure Ω)
    (F : ι → Ω → Matrix (Fin a) (Fin b) ℝ)
    (hF : ∀ i r s, Measurable (fun x => F i x r s))
    (hi : ∀ i, Integrable (fun x => ‖F i x‖^2) μ)
    (ho : ∀ i j, i ≠ j → ∀ r s, (∫ x, F i x r s * F j x r s ∂μ) = 0) :
    Integrable (fun x => ‖∑ i, F i x‖^2) μ ∧
    (∫ x, ‖∑ i, F i x‖^2 ∂μ) = ∑ i, ∫ x, ‖F i x‖^2 ∂μ :=
  matrix_orthogonal_second_moment μ F
    (fun i j r s => matrix_entry_pair_integrable μ (F i) (F j) (hF i) (hF j) (hi i) (hi j) r s) ho

#print axioms matrix_orthogonal_second_moment_of_squares
end SpectralRadiusUpperTail
