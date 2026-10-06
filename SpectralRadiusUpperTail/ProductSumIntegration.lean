import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.FunProp

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma bounded_shift_product_integrable (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : E → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B)
    (φ : α → E) (ψ : β → E) (hφ : Measurable φ) (hψ : Measurable ψ) (s : E) :
    Integrable (fun p : α × β => f (s+φ p.1+ψ p.2)) (μ.prod ν) := by
  have hm : Measurable (fun p : α × β => f (s+φ p.1+ψ p.2)) :=
    hf.comp ((measurable_const.add (hφ.comp measurable_fst)).add (hψ.comp measurable_snd))
  apply (integrable_const B).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs] using hB (s+φ p.1+ψ p.2))

lemma measurable_finite_sum {N : ℕ} (φ : Fin N → α → E)
    (hφ : ∀ i, Measurable (φ i)) :
    Measurable (fun x : Fin N → α => ∑ i, φ i (x i)) :=
  Finset.measurable_sum _ (fun i _ => (hφ i).comp (measurable_pi_apply i))

/-- Exact head/tail integration of an actual finite product sum. Joint
integrability follows from the bounded test before applying Fubini. -/
theorem product_sum_integral_succ (N : ℕ) (μ : Fin (N+1) → Measure α)
    [∀ i, IsProbabilityMeasure (μ i)]
    (φ : Fin (N+1) → α → E) (hφ : ∀ i, Measurable (φ i))
    (f : E → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) (s : E) :
    (∫ x : Fin (N+1) → α, f (s+∑ i, φ i (x i)) ∂Measure.pi μ) =
      ∫ x : α, ∫ y : Fin N → α, f (s+φ 0 x+∑ i, φ i.succ (y i))
        ∂Measure.pi (fun i : Fin N => μ i.succ) ∂μ 0 := by
  have hi := bounded_shift_product_integrable (μ 0)
    (Measure.pi (fun i : Fin N => μ i.succ)) f hf B hB
    (φ 0) (fun y : Fin N → α => ∑ i, φ i.succ (y i)) (hφ 0)
    (measurable_finite_sum _ (fun i => hφ i.succ)) s
  calc
    _ = ∫ p : α × (Fin N → α), f (s+φ 0 p.1+∑ i, φ i.succ (p.2 i))
        ∂(μ 0).prod (Measure.pi (fun i : Fin N => μ i.succ)) := by
      rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).integral_comp']
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.sum_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
        Fin.zero_succAbove, Fin.cons_zero, cast_eq, add_assoc]
    _ = _ := integral_prod _ hi

lemma integral_difference_of_pointwise (μ : Measure α) [IsProbabilityMeasure μ]
    (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (C : ℝ) (hC : ∀ x, |f x-g x| ≤ C) :
    |(∫ x, f x ∂μ)-(∫ x, g x ∂μ)| ≤ C := by
  rw [← integral_sub hf hg]
  have hh := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => f x-g x)
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hC x))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hh

#print axioms product_sum_integral_succ
#print axioms integral_difference_of_pointwise
end SpectralRadiusUpperTail
