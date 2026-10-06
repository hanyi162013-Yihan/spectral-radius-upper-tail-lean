import SpectralRadiusUpperTail.SchurWaitingCount
import SpectralRadiusUpperTail.FiniteSumSecondMoment
import SpectralRadiusUpperTail.SpectralWitness

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

noncomputable instance schurWaitingTimesFintype (k l : ℕ) : Fintype (SchurWaitingTimes k l) :=
  Fintype.ofEquiv (Sym (Fin (l+1)) (k-l)) (Sym.equivNatSumOfFintype (Fin (l+1)) (k-l))

lemma finite_matrix_sum_second_moment {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] {d : ℕ} (μ : Measure Ω)
    (F : ι → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hF : ∀ i a b, Measurable (fun x => F i x a b))
    (hi : ∀ i, Integrable (fun x => ‖F i x‖^2) μ)
    (B : ℝ) (hB : ∀ i, (∫ x, ‖F i x‖^2 ∂μ) ≤ B) :
    Integrable (fun x => ‖∑ i, F i x‖^2) μ ∧
      (∫ x, ‖∑ i, F i x‖^2 ∂μ) ≤ (Fintype.card ι : ℝ)^2*B := by
  classical
  have henv : Integrable (fun x => (Fintype.card ι : ℝ)*∑ i, ‖F i x‖^2) μ :=
    (integrable_finsetSum _ (fun i _ => hi i)).const_mul _
  have hm : Measurable (fun x => ‖∑ i, F i x‖^2) := by
    simp_rw [real_frobenius_norm_sq, Matrix.sum_apply]
    exact Finset.measurable_sum _ (fun a _ => Finset.measurable_sum _ (fun b _ =>
      (Finset.measurable_sum _ (fun i _ => hF i a b)).pow_const 2))
  have hf := henv.mono_nonneg hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall (fun x => norm_finite_sum_sq_le (fun i => F i x)))
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∫ x, (Fintype.card ι : ℝ)*∑ i, ‖F i x‖^2 ∂μ :=
      integral_mono hf henv (fun x => norm_finite_sum_sq_le (fun i => F i x))
    _ = (Fintype.card ι : ℝ)*∑ i, ∫ x, ‖F i x‖^2 ∂μ := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)]
    _ ≤ (Fintype.card ι : ℝ)*∑ _i : ι, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hB i)) (Nat.cast_nonneg _)
    _ = _ := by simp [pow_two, mul_assoc]

/-- Summing all waiting-time compositions along one Schur path costs
choose(k,l)^2. Dependence between the waiting-time terms is allowed. -/
theorem schur_waiting_sum_second_moment {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (μ : Measure Ω) (k l : ℕ) (hlk : l ≤ k)
    (F : SchurWaitingTimes k l → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hF : ∀ i a b, Measurable (fun x => F i x a b))
    (hi : ∀ i, Integrable (fun x => ‖F i x‖^2) μ)
    (B : ℝ) (hB : ∀ i, (∫ x, ‖F i x‖^2 ∂μ) ≤ B) :
    Integrable (fun x => ‖∑ i, F i x‖^2) μ ∧
      (∫ x, ‖∑ i, F i x‖^2 ∂μ) ≤ (k.choose l : ℝ)^2*B := by
  have hc : Fintype.card (SchurWaitingTimes k l) = k.choose l := by
    rw [← Nat.card_eq_fintype_card]
    exact schurWaitingTimes_card k l hlk
  simpa only [hc] using finite_matrix_sum_second_moment μ F hF hi B hB

#print axioms finite_matrix_sum_second_moment
#print axioms schur_waiting_sum_second_moment
end SpectralRadiusUpperTail
