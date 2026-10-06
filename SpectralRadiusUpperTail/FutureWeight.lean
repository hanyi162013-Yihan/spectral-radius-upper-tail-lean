import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Analysis.SpecialFunctions.Exp

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

section Future
variable {α E : Type*} [MeasurableSpace α] [MeasurableSpace E] [Sub E] [MeasurableSub₂ E]

noncomputable def futureWeight (μ : Measure α) (f : ℕ → α → E) (w : E → ℝ≥0∞) :
    ℕ → E → ℝ≥0∞
  | 0, s => w s
  | n+1, s => ∫⁻ x, futureWeight μ f w n (s-f n x) ∂μ

lemma futureWeight_measurable (μ : Measure α) [SFinite μ] (f : ℕ → α → E)
    (w : E → ℝ≥0∞) (hf : ∀ n, Measurable (f n)) (hw : Measurable w) (n : ℕ) :
    Measurable (futureWeight μ f w n) := by
  induction n with
  | zero => exact hw
  | succ n ih =>
    have h : Measurable (fun z : E × α => futureWeight μ f w n (z.1-f n z.2)) :=
      ih.comp (measurable_fst.sub ((hf n).comp measurable_snd))
    exact h.lintegral_prod_right'

lemma futureWeight_le_one (μ : Measure α) [IsProbabilityMeasure μ] (f : ℕ → α → E)
    (w : E → ℝ≥0∞) (hw : ∀ s, w s ≤ 1) (n : ℕ) (s : E) :
    futureWeight μ f w n s ≤ 1 := by
  induction n generalizing s with
  | zero => exact hw s
  | succ n ih =>
    calc
      _ ≤ ∫⁻ _x : α, (1:ℝ≥0∞) ∂μ := lintegral_mono (fun x => ih (s-f n x))
      _ = 1 := by simp

lemma lintegral_pos_of_everywhere_pos (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ≥0∞) (hf : Measurable f) (hpos : ∀ x, 0 < f x) :
    0 < ∫⁻ x, f x ∂μ := by
  apply (lintegral_pos_iff_support hf).mpr
  have hs : Function.support f = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (hpos x)
  rw [hs, measure_univ]
  exact zero_lt_one

lemma futureWeight_pos (μ : Measure α) [IsProbabilityMeasure μ] (f : ℕ → α → E)
    (w : E → ℝ≥0∞) (hf : ∀ n, Measurable (f n)) (hw : Measurable w)
    (hpos : ∀ s, 0 < w s) (n : ℕ) (s : E) : 0 < futureWeight μ f w n s := by
  induction n generalizing s with
  | zero => exact hpos s
  | succ n ih =>
    apply lintegral_pos_of_everywhere_pos μ _
      ((futureWeight_measurable μ f w hf hw n).comp (measurable_const.sub (hf n)))
    intro x
    exact ih (s-f n x)

end Future

section Gaussian
variable {E : Type*} [NormedAddCommGroup E]

noncomputable def gaussianSoftWeight (a : ℝ) (s : E) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-‖s‖ ^ 2 / a))

lemma gaussianSoftWeight_pos (a : ℝ) (s : E) : 0 < gaussianSoftWeight a s :=
  ENNReal.ofReal_pos.mpr (Real.exp_pos _)

lemma gaussianSoftWeight_le_one (a : ℝ) (ha : 0 < a) (s : E) :
    gaussianSoftWeight a s ≤ 1 := by
  have h : Real.exp (-‖s‖ ^ 2 / a) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) ha.le)
  simpa only [gaussianSoftWeight, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal h

variable [MeasurableSpace E] [BorelSpace E]

lemma gaussianSoftWeight_measurable (a : ℝ) : Measurable (gaussianSoftWeight (E := E) a) :=
  (Real.continuous_exp.comp ((continuous_norm.pow 2).neg.div_const a)).measurable.ennreal_ofReal

end Gaussian

#print axioms futureWeight_pos
#print axioms gaussianSoftWeight_measurable
end SpectralRadiusUpperTail
