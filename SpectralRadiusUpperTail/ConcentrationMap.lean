import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real

namespace SpectralRadiusUpperTail
open MeasureTheory

lemma centered_tail_map {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) (ν : Measure E) (T : Ω → E) (hT : Measurable T)
    (hmap : μ.map T = ν) (f : E → ℝ) (hf : Measurable f) (δ : ℝ) :
    μ.real {x | δ < |f (T x)-(∫ y, f (T y) ∂μ)|} =
      ν.real {x | δ < |f x-(∫ y, f y ∂ν)|} := by
  have hi : (∫ y, f (T y) ∂μ) = ∫ y, f y ∂ν := by
    rw [← hmap, integral_map hT.aemeasurable hf.aestronglyMeasurable]
  have hs : MeasurableSet {x | δ < |f x-(∫ y, f y ∂ν)|} :=
    measurableSet_lt measurable_const (by simpa only [Real.norm_eq_abs] using (hf.sub_const (∫ y, f y ∂ν)).norm)
  have he := map_measureReal_apply (μ := μ) hT hs
  rw [hmap] at he
  simpa only [hi, Set.preimage_setOf_eq] using he.symm

#print axioms centered_tail_map
end SpectralRadiusUpperTail
