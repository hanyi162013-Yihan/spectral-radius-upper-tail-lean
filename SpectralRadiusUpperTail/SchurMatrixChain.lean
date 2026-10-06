import SpectralRadiusUpperTail.SpectralWitness
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.FunProp

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

/-- An ordered nonempty product; retaining a first factor avoids an
artificial dimension factor from the Frobenius norm of the identity. -/
def matrixChain {d : ℕ} : (m : ℕ) → (Fin (m+1) → Matrix (Fin d) (Fin d) ℝ) →
    Matrix (Fin d) (Fin d) ℝ
  | 0, F => F 0
  | m+1, F => F 0 * matrixChain m (fun i => F i.succ)

lemma matrixChain_norm_sq_le {d : ℕ} (m : ℕ)
    (F : Fin (m+1) → Matrix (Fin d) (Fin d) ℝ) :
    ‖matrixChain m F‖^2 ≤ ∏ i, ‖F i‖^2 := by
  induction m with
  | zero => simp [matrixChain]
  | succ m ih =>
    rw [matrixChain, Fin.prod_univ_succ]
    calc
      _ ≤ (‖F 0‖*‖matrixChain m (fun i => F i.succ)‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (Matrix.frobenius_norm_mul _ _) 2
      _ ≤ _ := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left (ih _) (sq_nonneg _)

lemma matrixChain_entry_measurable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (m : ℕ)
    (F : Fin (m+1) → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hF : ∀ i a b, Measurable (fun x => F i x a b)) (a b : Fin d) :
    Measurable (fun x => matrixChain m (fun i => F i x) a b) := by
  induction m generalizing a b with
  | zero => exact hF 0 a b
  | succ m ih =>
    simp only [matrixChain, Matrix.mul_apply]
    exact Finset.measurable_sum _ (fun j _ => (hF 0 a j).mul
      (ih (fun i => F i.succ) (fun i => hF i.succ) j b))

lemma matrixChain_norm_sq_measurable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (m : ℕ)
    (F : Fin (m+1) → Ω → Matrix (Fin d) (Fin d) ℝ)
    (hF : ∀ i a b, Measurable (fun x => F i x a b)) :
    Measurable (fun x => ‖matrixChain m (fun i => F i x)‖^2) := by
  simp_rw [real_frobenius_norm_sq]
  exact Finset.measurable_sum _ (fun a _ => Finset.measurable_sum _ (fun b _ =>
    (matrixChain_entry_measurable m F hF a b).pow_const 2))

/-- Independent matrix factors: the squared Hilbert--Schmidt expectation
of their ordered product is at most the product of their second moments.
No independence between entire Schur paths is assumed. -/
theorem independent_matrixChain_second_moment {d : ℕ} (m : ℕ)
    {E : Fin (m+1) → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : (i : Fin (m+1)) → Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (F : (i : Fin (m+1)) → E i → Matrix (Fin d) (Fin d) ℝ)
    (hF : ∀ i a b, Measurable (fun x => F i x a b))
    (hi : ∀ i, Integrable (fun x => ‖F i x‖^2) (μ i)) :
    Integrable (fun x => ‖matrixChain m (fun i => F i (x i))‖^2) (Measure.pi μ) ∧
    (∫ x, ‖matrixChain m (fun i => F i (x i))‖^2 ∂Measure.pi μ) ≤
      ∏ i, ∫ x, ‖F i x‖^2 ∂μ i := by
  have hp := Integrable.fintype_prod_dep hi
  have hm := matrixChain_norm_sq_measurable m (fun i (x : (j : Fin (m+1)) → E j) => F i (x i))
    (fun i a b => (hF i a b).comp (measurable_pi_apply i))
  have hf := hp.mono_nonneg hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall (fun x => matrixChain_norm_sq_le m (fun i => F i (x i))))
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∫ x, ∏ i, ‖F i (x i)‖^2 ∂Measure.pi μ :=
      integral_mono hf hp (fun x => matrixChain_norm_sq_le m (fun i => F i (x i)))
    _ = _ := integral_fintype_prod_eq_prod (μ := μ) (fun i x => ‖F i x‖^2)

#print axioms matrixChain_norm_sq_le
#print axioms independent_matrixChain_second_moment
end SpectralRadiusUpperTail
