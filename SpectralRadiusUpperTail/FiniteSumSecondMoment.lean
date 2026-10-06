import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

lemma norm_finite_sum_sq_le {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (F : ι → E) : ‖∑ i, F i‖^2 ≤ (Fintype.card ι : ℝ)*∑ i, ‖F i‖^2 := by
  classical
  calc
    _ ≤ (∑ i, ‖F i‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
        (fun i => ‖F i‖) (fun _ => (1 : ℝ))
      simpa [mul_comm] using h

/-- A finite sum needs no independence: Cauchy--Schwarz costs the square
of the number of summands if every summand has second moment at most B. -/
theorem finite_sum_second_moment_bound {ι Ω E : Type*} [Fintype ι]
    [MeasurableSpace Ω] [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) (F : ι → Ω → E) (hF : ∀ i, Measurable (F i))
    (hi : ∀ i, Integrable (fun x => ‖F i x‖^2) μ)
    (B : ℝ) (hB : ∀ i, (∫ x, ‖F i x‖^2 ∂μ) ≤ B) :
    Integrable (fun x => ‖∑ i, F i x‖^2) μ ∧
      (∫ x, ‖∑ i, F i x‖^2 ∂μ) ≤ (Fintype.card ι : ℝ)^2*B := by
  classical
  have henv : Integrable (fun x => (Fintype.card ι : ℝ)*∑ i, ‖F i x‖^2) μ :=
    (integrable_finsetSum _ (fun i _ => hi i)).const_mul _
  have hm : Measurable (fun x => ‖∑ i, F i x‖^2) :=
    (Finset.measurable_sum _ (fun i _ => hF i)).norm.pow_const 2
  have hf := henv.mono_nonneg hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall (fun x => norm_finite_sum_sq_le (fun i => F i x)))
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∫ x, (Fintype.card ι : ℝ)*∑ i, ‖F i x‖^2 ∂μ :=
      integral_mono hf henv (fun x => norm_finite_sum_sq_le (fun i => F i x))
    _ = (Fintype.card ι : ℝ)*∑ i, ∫ x, ‖F i x‖^2 ∂μ := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)]
    _ ≤ (Fintype.card ι : ℝ)*∑ _i : ι, B := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hB i)) (Nat.cast_nonneg _)
    _ = _ := by simp [pow_two, mul_assoc]

#print axioms norm_finite_sum_sq_le
#print axioms finite_sum_second_moment_bound
end SpectralRadiusUpperTail
