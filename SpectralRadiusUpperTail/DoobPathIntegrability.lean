import SpectralRadiusUpperTail.ConcreteDoobCoupling
import Mathlib.MeasureTheory.Function.L1Space.Integrable

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bounded terminal weight preserves integrability at every finite history.
This applies to the explicit path law, not merely to an unspecified coupling. -/
lemma doobCoupledPathLaw_source_integrable (μ : Measure α) [IsProbabilityMeasure μ]
    (N : ℕ) (A : (n : ℕ) → (Fin n → α) → ℝ≥0∞)
    (hA : ∀ n, Measurable (A n))
    (hzero : ∀ n ≤ N, ∀ s, A n s ≠ 0) (htop : ∀ n ≤ N, ∀ s, A n s ≠ ∞)
    (hrec : ∀ n < N, ∀ s, (∫⁻ x, A (n+1) (Fin.cons x s) ∂μ) = A n s)
    (hle : ∀ n ≤ N, ∀ s, A n s ≤ 1) (n : ℕ) (hn : n ≤ N)
    (f : (Fin n → α) → E) (hf : Integrable f (Measure.pi (fun _ : Fin n => μ))) :
    Integrable (fun s => f (coordinateVector Prod.fst n s)) (doobCoupledPathLaw μ N A hA n) := by
  have hdom : (Measure.pi (fun _ : Fin n => μ)).withDensity
      (fun s => A n s/A 0 (fun i => Fin.elim0 i)) ≤
        (A 0 (fun i => Fin.elim0 i))⁻¹ • Measure.pi (fun _ : Fin n => μ) := by
    calc
      _ ≤ (Measure.pi (fun _ : Fin n => μ)).withDensity
          (fun _ => (A 0 (fun i => Fin.elim0 i))⁻¹) := by
        apply withDensity_mono
        exact Filter.Eventually.of_forall (fun s => by
          simpa only [one_div] using ENNReal.div_le_div_right (hle n hn s)
            (A 0 (fun i => Fin.elim0 i)))
      _ = _ := withDensity_const _
  have hi := (hf.smul_measure (ENNReal.inv_ne_top.mpr (hzero 0 (Nat.zero_le N) _))).mono_measure hdom
  have hm := doobCoupledPathLaw_source μ N A hA hzero htop hrec n hn
  rw [← hm] at hi
  exact hi.comp_measurable (measurable_coordinateVector Prod.fst measurable_fst n)

lemma doobCoupledPathLaw_comparator_integrable (μ : Measure α) [IsProbabilityMeasure μ]
    (N : ℕ) (A : (n : ℕ) → (Fin n → α) → ℝ≥0∞)
    (hA : ∀ n, Measurable (A n))
    (hzero : ∀ n ≤ N, ∀ s, A n s ≠ 0) (htop : ∀ n ≤ N, ∀ s, A n s ≠ ∞)
    (hrec : ∀ n < N, ∀ s, (∫⁻ x, A (n+1) (Fin.cons x s) ∂μ) = A n s)
    (n : ℕ) (f : (Fin n → α) → E)
    (hf : Integrable f (Measure.pi (fun _ : Fin n => μ))) :
    Integrable (fun s => f (comparatorVector n s)) (doobCoupledPathLaw μ N A hA n) := by
  rw [← doobCoupledPathLaw_comparator μ N A hA hzero htop hrec n] at hf
  exact hf.comp_measurable (measurable_comparatorVector n)

#print axioms doobCoupledPathLaw_source_integrable
end SpectralRadiusUpperTail
