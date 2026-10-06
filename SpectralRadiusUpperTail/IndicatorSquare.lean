import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

namespace SpectralRadiusUpperTail
variable {Ω E : Type*} [NormedAddCommGroup E]

lemma indicator_norm_sq_eq (A : Set Ω) (f : Ω → E) :
    (fun x => ‖A.indicator f x‖^2) = A.indicator (fun x => ‖f x‖^2) := by
  funext x
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, norm_zero]
    norm_num

#print axioms indicator_norm_sq_eq
end SpectralRadiusUpperTail
