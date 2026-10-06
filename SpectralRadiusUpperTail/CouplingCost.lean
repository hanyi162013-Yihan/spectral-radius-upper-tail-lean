import SpectralRadiusUpperTail.CommonPartCoupling
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic.Ring

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]

lemma lintegral_fst_product (p q : Measure α) [IsFiniteMeasure p] [IsFiniteMeasure q]
    (f : α → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z.1 ∂p.prod q) = q Set.univ * ∫⁻ x, f x ∂p := by
  calc
    _ = ∫⁻ x, f x ∂(p.prod q).map Prod.fst :=
      (lintegral_map hf measurable_fst).symm
    _ = _ := by rw [Measure.map_fst_prod, lintegral_smul_measure, smul_eq_mul]

lemma lintegral_snd_product (p q : Measure α) [IsFiniteMeasure p] [IsFiniteMeasure q]
    (f : α → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f z.2 ∂p.prod q) = p Set.univ * ∫⁻ x, f x ∂q := by
  calc
    _ = ∫⁻ x, f x ∂(p.prod q).map Prod.snd :=
      (lintegral_map hf measurable_snd).symm
    _ = _ := by rw [Measure.map_snd_prod, lintegral_smul_measure, smul_eq_mul]

lemma commonPartCoupling_cost_eq (τ p q : Measure α) (c : α × α → ℝ≥0∞)
    (hc : Measurable c) (hdiag : ∀ x, c (x,x) = 0) :
    (∫⁻ z, c z ∂commonPartCoupling τ p q) =
      (p Set.univ)⁻¹ * ∫⁻ z, c z ∂p.prod q := by
  unfold commonPartCoupling
  rw [lintegral_add_measure,
    lintegral_map hc
      (show Measurable (fun x : α => (x,x)) from measurable_id.prodMk measurable_id),
    lintegral_smul_measure, smul_eq_mul]
  simp only [hdiag, lintegral_zero, zero_add]

/-- An actual coupling-cost bound. It also covers zero residual mass and
infinite cost integrals, without cancelling a possibly zero mass. -/
theorem commonPartCoupling_cost_le (τ p q : Measure α)
    [IsFiniteMeasure p] [IsFiniteMeasure q] (hmass : q Set.univ = p Set.univ)
    (c : α × α → ℝ≥0∞) (f : α → ℝ≥0∞)
    (hc : Measurable c) (hf : Measurable f)
    (hdiag : ∀ x, c (x,x) = 0)
    (hcost : ∀ z, c z ≤ 2 * (f z.1 + f z.2)) :
    (∫⁻ z, c z ∂commonPartCoupling τ p q) ≤
      2 * ((∫⁻ x, f x ∂p) + ∫⁻ x, f x ∂q) := by
  have hfst : Measurable (fun z : α × α => f z.1) := hf.comp measurable_fst
  have hsum : Measurable (fun z : α × α => f z.1 + f z.2) :=
    (hf.comp measurable_fst).add (hf.comp measurable_snd)
  rw [commonPartCoupling_cost_eq τ p q c hc hdiag]
  calc
    _ ≤ (p Set.univ)⁻¹ * ∫⁻ z, 2 * (f z.1 + f z.2) ∂p.prod q :=
      mul_le_mul' le_rfl (lintegral_mono hcost)
    _ = (p Set.univ)⁻¹ *
        (2 * (q Set.univ * (∫⁻ x, f x ∂p) + p Set.univ * (∫⁻ x, f x ∂q))) := by
      rw [lintegral_const_mul 2 hsum,
        lintegral_add_left hfst,
        lintegral_fst_product p q f hf, lintegral_snd_product p q f hf]
    _ = ((p Set.univ)⁻¹ * p Set.univ) *
        (2 * ((∫⁻ x, f x ∂p) + ∫⁻ x, f x ∂q)) := by rw [hmass]; ring
    _ ≤ 1 * (2 * ((∫⁻ x, f x ∂p) + ∫⁻ x, f x ∂q)) :=
      mul_le_mul' (ENNReal.inv_mul_le_one _) le_rfl
    _ = _ := one_mul _

#print axioms commonPartCoupling_cost_le
end SpectralRadiusUpperTail
