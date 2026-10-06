import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

/-- Exact finite Parseval identity from vanishing cross integrals.
The functions need not be independent. -/
theorem finite_orthogonal_second_moment {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (μ : Measure Ω) (F : ι → Ω → ℝ)
    (hi : ∀ i j, Integrable (fun x => F i x*F j x) μ)
    (ho : ∀ i j, i ≠ j → (∫ x, F i x*F j x ∂μ) = 0) :
    Integrable (fun x => (∑ i, F i x)^2) μ ∧
      (∫ x, (∑ i, F i x)^2 ∂μ) = ∑ i, ∫ x, (F i x)^2 ∂μ := by
  classical
  have he (x : Ω) : (∑ i, F i x)^2 = ∑ i, ∑ j, F i x*F j x := by
    rw [pow_two, Finset.sum_mul_sum]
  have hp (i : ι) : Integrable (fun x => ∑ j, F i x*F j x) μ :=
    integrable_finsetSum _ (fun j _ => hi i j)
  constructor
  · simp_rw [he]
    exact integrable_finsetSum _ (fun i _ => hp i)
  · simp_rw [he]
    rw [integral_finsetSum _ (fun i _ => hp i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hi i j)]
    rw [Finset.sum_eq_single i]
    · simp only [pow_two]
    · intro j _ hji
      exact ho i j hji.symm
    · simp

#print axioms finite_orthogonal_second_moment
end SpectralRadiusUpperTail
