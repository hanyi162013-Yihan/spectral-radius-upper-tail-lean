import SpectralRadiusUpperTail.ConditionalValuePullback
import Mathlib.MeasureTheory.Integral.Prod

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory
variable {Ω Θ E : Type*} [mΩ : MeasurableSpace Ω] [mΘ : MeasurableSpace Θ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma partialProductSigma_le (m : MeasurableSpace Ω) (hm : m ≤ mΩ) :
    m.prod mΘ ≤ mΩ.prod mΘ :=
  sup_le_sup (MeasurableSpace.comap_mono hm) le_rfl

/-- Fully revealing an independent second factor preserves a conditional-zero
identity on the first factor, even with a partially revealed first history. -/
theorem condExp_prod_fst_zero (P : Measure Ω) [IsFiniteMeasure P]
    (Q : Measure Θ) [IsFiniteMeasure Q] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (f : Ω → E) (hf : Integrable f P) (hz : P[f | m] =ᵐ[P] 0) :
    (@Measure.prod Ω Θ mΩ mΘ P Q)[(fun z => f z.1) | m.prod mΘ] =ᵐ[@Measure.prod Ω Θ mΩ mΘ P Q] 0 := by
  letI : MeasurableSpace Ω := mΩ
  have hi := hf.comp_fst Q
  have hle := partialProductSigma_le (mΘ := mΘ) m hm
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hle hi ?_ ?_ ?_
  · intro A _ _
    exact integrableOn_zero
  · intro A hA _
    have hA0 := hle _ hA
    simp only [Pi.zero_apply, integral_zero]
    rw [← integral_indicator hA0]
    rw [integral_prod_symm _ (hi.indicator hA0)]
    have hzsection (y : Θ) : ∫ x, A.indicator (fun z => f z.1) (x,y) ∂P = 0 := by
      let B := (fun x : Ω => (x,y)) ⁻¹' A
      have hB : MeasurableSet[m] B :=
        @measurable_prodMk_right Ω Θ m mΘ y _ hA
      change ∫ x, B.indicator f x ∂P = 0
      rw [integral_indicator (hm _ hB), ← setIntegral_condExp hm hf hB]
      rw [integral_congr_ae (ae_restrict_of_ae hz)]
      simp
    simp only [hzsection, integral_zero]
  · exact aestronglyMeasurable_const

/-- The actual conditional value is unchanged when an independent factor is
fully observed. This supplies the bridge from row history to matrix history. -/
theorem condExp_prod_fst (P : Measure Ω) [IsFiniteMeasure P]
    (Q : Measure Θ) [IsFiniteMeasure Q] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (f : Ω → E) (hf : Integrable f P) :
    (@Measure.prod Ω Θ mΩ mΘ P Q)[(fun z => f z.1) | m.prod mΘ] =ᵐ[@Measure.prod Ω Θ mΩ mΘ P Q]
      fun z => (P[f | m]) z.1 := by
  letI : MeasurableSpace Ω := mΩ
  let g := P[f | m]
  have hg : Integrable g P := integrable_condExp
  have hgm : StronglyMeasurable[m] g := stronglyMeasurable_condExp
  have hz : P[f-g | m] =ᵐ[P] 0 := by
    have hs := condExp_sub hf hg m
    rw [condExp_of_stronglyMeasurable hm hgm hg] at hs
    filter_upwards [hs] with x hx
    simpa only [Pi.sub_apply, g, sub_self, Pi.zero_apply] using hx
  have hp := condExp_prod_fst_zero P Q m hm (f-g) (hf.sub hg) hz
  have hgp := hg.comp_fst Q
  have hgm' : StronglyMeasurable[m.prod mΘ] (fun z : Ω × Θ => g z.1) :=
    hgm.comp_measurable (@measurable_fst Ω Θ m mΘ)
  have hs := condExp_sub (hf.comp_fst Q) hgp (m.prod mΘ)
  rw [condExp_of_stronglyMeasurable (partialProductSigma_le m hm) hgm' hgp] at hs
  filter_upwards [hs,hp] with z hz hpz
  exact sub_eq_zero.mp (hz.symm.trans hpz)

#print axioms condExp_prod_fst_zero
#print axioms condExp_prod_fst
end SpectralRadiusUpperTail
