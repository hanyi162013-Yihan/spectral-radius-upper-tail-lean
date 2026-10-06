import SpectralRadiusUpperTail.TwoSidedDensityLaw
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic.Ring

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {Θ α β : Type*} [MeasurableSpace Θ] [MeasurableSpace α] [MeasurableSpace β]

lemma map_withDensity_pullback (P : Measure α) (f : α → β) (w : β → ℝ≥0∞)
    (hf : Measurable f) (hw : Measurable w) :
    (P.withDensity (fun x => w (f x))).map f = (P.map f).withDensity w := by
  ext A hA
  rw [Measure.map_apply hf hA, withDensity_apply _ (hf hA), withDensity_apply _ hA,
    setLIntegral_map hA hw hf]

lemma densityKernel_compProd (P : Measure Θ) [SFinite P]
    (μ : Measure α) [IsProbabilityMeasure μ] (k : Θ → α → ℝ≥0∞)
    (hk : Measurable (Function.uncurry k)) (hnorm : ∀ s, (∫⁻ x, k s x ∂μ) = 1) :
    P ⊗ₘ (densityKernel μ k hk) = (P.prod μ).withDensity (Function.uncurry k) := by
  have heq : densityKernel μ k hk = (Kernel.const Θ μ).withDensity k := by
    ext s
    rw [Kernel.withDensity_apply _ hk]
    rfl
  have : IsMarkovKernel ((Kernel.const Θ μ).withDensity k) :=
    heq ▸ densityKernel_markov μ k hk hnorm
  rw [heq, Measure.compProd_withDensity hk, Measure.compProd_const]
  rfl

lemma weighted_densityKernel_compProd (P : Measure Θ) [SFinite P]
    (μ : Measure α) [IsProbabilityMeasure μ] (g : Θ → ℝ≥0∞) (hg : Measurable g)
    (k : Θ → α → ℝ≥0∞) (hk : Measurable (Function.uncurry k))
    (hnorm : ∀ s, (∫⁻ x, k s x ∂μ) = 1) :
    (P.withDensity g) ⊗ₘ (densityKernel μ k hk) =
      (P.prod μ).withDensity (fun z => g z.1 * k z.1 z.2) := by
  rw [densityKernel_compProd (P.withDensity g) μ k hk hnorm, prod_withDensity_left hg]
  have hgf : Measurable (fun z : Θ × α => g z.1) := hg.comp measurable_fst
  rw [← withDensity_mul (P.prod μ) hgf hk]
  rfl

lemma density_ratio_cancel (a b c : ℝ≥0∞) (ha0 : a ≠ 0) (hat : a ≠ ∞) :
    (a/c) * (b/a) = b/c := by
  simp only [div_eq_mul_inv]
  calc
    a * c⁻¹ * (b * a⁻¹) = (a * a⁻¹) * (b * c⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel ha0 hat, one_mul]

lemma density_ratio_normalized (μ : Measure α) (B : α → ℝ≥0∞) (a : ℝ≥0∞)
    (ha0 : a ≠ 0) (hat : a ≠ ∞) (hrec : (∫⁻ x, B x ∂μ) = a) :
    (∫⁻ x, B x / a ∂μ) = 1 := by
  simp only [div_eq_mul_inv]
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr ha0), hrec,
    ENNReal.mul_inv_cancel ha0 hat]

#print axioms weighted_densityKernel_compProd
#print axioms density_ratio_normalized
end SpectralRadiusUpperTail
