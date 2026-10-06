import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]

/-- Couple a common part diagonally and equal-mass residuals by their product.
The formula also works at zero residual mass, because the residual measures vanish. -/
noncomputable def commonPartCoupling (τ p q : Measure α) : Measure (α × α) :=
  τ.map (fun x => (x,x)) + (p Set.univ)⁻¹ • p.prod q

lemma inverse_mass_smul (p : Measure α) [IsFiniteMeasure p] :
    (p Set.univ)⁻¹ • ((p Set.univ) • p) = p := by
  by_cases hp : p Set.univ = 0
  · have hpzero : p = 0 := Measure.measure_univ_eq_zero.mp hp
    simp [hpzero]
  · rw [smul_smul, ENNReal.inv_mul_cancel hp (measure_ne_top p Set.univ), one_smul]

theorem commonPartCoupling_map_fst (τ p q : Measure α)
    [IsFiniteMeasure p] [IsFiniteMeasure q] (hmass : q Set.univ = p Set.univ) :
    (commonPartCoupling τ p q).map Prod.fst = τ + p := by
  unfold commonPartCoupling
  rw [Measure.map_add _ _ measurable_fst, Measure.map_smul,
    Measure.map_map measurable_fst
      (show Measurable (fun x : α => (x,x)) from measurable_id.prodMk measurable_id)]
  simp only [Function.comp_def, Measure.map_id', Measure.map_fst_prod, hmass]
  rw [inverse_mass_smul]

theorem commonPartCoupling_map_snd (τ p q : Measure α)
    [IsFiniteMeasure p] [IsFiniteMeasure q] (hmass : q Set.univ = p Set.univ) :
    (commonPartCoupling τ p q).map Prod.snd = τ + q := by
  unfold commonPartCoupling
  rw [Measure.map_add _ _ measurable_snd, Measure.map_smul,
    Measure.map_map measurable_snd
      (show Measurable (fun x : α => (x,x)) from measurable_id.prodMk measurable_id)]
  simp only [Function.comp_def, Measure.map_id', Measure.map_snd_prod]
  rw [← hmass, inverse_mass_smul]

theorem commonPartCoupling_probability (τ p q : Measure α)
    [IsFiniteMeasure p] [IsFiniteMeasure q] (hmass : q Set.univ = p Set.univ)
    (hnorm : (τ+p) Set.univ = 1) : IsProbabilityMeasure (commonPartCoupling τ p q) := by
  constructor
  have h := congrArg (fun ν : Measure α => ν Set.univ)
    (commonPartCoupling_map_fst τ p q hmass)
  simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,
    Set.preimage_univ, hnorm] using h

#print axioms commonPartCoupling_map_fst
#print axioms commonPartCoupling_map_snd
#print axioms commonPartCoupling_probability
end SpectralRadiusUpperTail
