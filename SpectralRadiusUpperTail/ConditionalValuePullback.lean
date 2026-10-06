import SpectralRadiusUpperTail.ConditionalPullback

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory
variable {Ω Θ E : Type*} [mΩ : MeasurableSpace Ω] [mΘ : MeasurableSpace Θ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Transport the actual conditional expectation value through an exact
joint-law projection, preserving the correct history sigma algebra. -/
theorem condExp_pullback_eq (P : Measure Ω) [IsFiniteMeasure P]
    (Q : Measure Θ) [IsFiniteMeasure Q] (T : Ω → Θ) (hT : Measurable T)
    (hmap : P.map T = Q) (m : MeasurableSpace Θ) (hm : m ≤ mΘ)
    (f g : Θ → E) (hf : Integrable f Q) (hg : Integrable g Q)
    (hgm : StronglyMeasurable[m] g) (hfg : Q[f | m] =ᵐ[Q] g) :
    P[f ∘ T | MeasurableSpace.comap T m] =ᵐ[P] g ∘ T := by
  letI : MeasurableSpace Θ := mΘ
  have hz : Q[f-g | m] =ᵐ[Q] 0 := by
    have hs := condExp_sub hf hg m
    rw [condExp_of_stronglyMeasurable hm hgm hg] at hs
    filter_upwards [hs,hfg] with x hx hfx
    simpa only [Pi.sub_apply, hfx, sub_self, Pi.zero_apply] using hx
  have hp := condExp_pullback_eq_zero P Q T hT hmap m hm (f-g) (hf.sub hg) hz
  have hfi : Integrable f (P.map T) := by rw [hmap]; exact hf
  have hgi : Integrable g (P.map T) := by rw [hmap]; exact hg
  have hfp := hfi.comp_measurable hT
  have hgp := hgi.comp_measurable hT
  have hle : MeasurableSpace.comap T m ≤ mΩ :=
    (MeasurableSpace.comap_mono hm).trans hT.comap_le
  have hgm' : StronglyMeasurable[MeasurableSpace.comap T m] (g ∘ T) :=
    hgm.comp_measurable (comap_measurable T)
  have hs := condExp_sub hfp hgp (MeasurableSpace.comap T m)
  rw [condExp_of_stronglyMeasurable hle hgm' hgp] at hs
  have hz' : P[(f ∘ T)-(g ∘ T) | MeasurableSpace.comap T m] =ᵐ[P] 0 := hp.2
  filter_upwards [hs,hz'] with x hx hz
  exact sub_eq_zero.mp (hx.symm.trans hz)

#print axioms condExp_pullback_eq
end SpectralRadiusUpperTail
