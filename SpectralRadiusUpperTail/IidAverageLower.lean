import SpectralRadiusUpperTail.ProductRowEnergy
import SpectralRadiusUpperTail.SecondMomentProbability

namespace SpectralRadiusUpperTail
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

lemma iid_sum_lower_probability_le {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (f : E → ℝ) (hf : MemLp f 2 μ)
    (q : ℝ) (hq : q < ∫ x, f x ∂μ) (n : ℕ) (hn : 0 < n) :
    (Measure.pi (fun _ : Fin n => μ)).real {x | (∑ i, f (x i)) ≤ (n : ℝ)*q} ≤
      ((∫ x, ‖f x-(∫ y, f y ∂μ)‖^2 ∂μ)/(∫ y, f y ∂μ-q)^2)/(n : ℝ) := by
  let m := ∫ x, f x ∂μ
  let F := fun x => f x-m
  have hF : MemLp F 2 μ := hf.sub (memLp_const m)
  have hm : (∫ x, F x ∂μ) = 0 := by
    rw [integral_sub (hf.integrable (by norm_num)) (integrable_const m)]
    simp [m]
  have hsum : MemLp (fun x : Fin n → E => ∑ i, F (x i)) 2 (Measure.pi (fun _ : Fin n => μ)) :=
    memLp_finsetSum Finset.univ (fun i _ => hF.comp_measurePreserving (measurePreserving_eval _ i))
  have hi := (memLp_two_iff_integrable_sq_norm hsum.aestronglyMeasurable).mp hsum
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hgap : 0 < m-q := sub_pos.mpr hq
  have hb := norm_probability_le_secondMoment (Measure.pi (fun _ : Fin n => μ))
    (fun x => ∑ i, F (x i)) hi ((n : ℝ)*(m-q)) (mul_pos hnpos hgap)
  have he := product_sum_norm_sq μ (fun _ : Fin n => F) (fun _ => hF) (fun _ => hm)
  rw [he] at hb
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hb
  have hsub : (Measure.pi (fun _ : Fin n => μ)).real {x | (∑ i, f (x i)) ≤ (n : ℝ)*q} ≤
      (Measure.pi (fun _ : Fin n => μ)).real {x | (n : ℝ)*(m-q) ≤ ‖∑ i, F (x i)‖} := by
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro x hx
    change (∑ i, f (x i)) ≤ (n : ℝ)*q at hx
    have hid : (∑ i : Fin n, F (x i)) = (∑ i, f (x i))-(n : ℝ)*m := by
      simp only [F,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    change (n : ℝ)*(m-q) ≤ ‖∑ i, F (x i)‖
    rw [hid,Real.norm_eq_abs]
    have hh := neg_le_abs ((∑ i, f (x i))-(n : ℝ)*m)
    linarith
  apply (hsub.trans hb).trans_eq
  dsimp only [F,m]
  field_simp
  <;> ring

lemma iid_sum_lower_probability_tendsto {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (f : E → ℝ) (hf : MemLp f 2 μ)
    (q : ℝ) (hq : q < ∫ x, f x ∂μ) :
    Tendsto (fun n => (Measure.pi (fun _ : Fin n => μ)).real
      {x | (∑ i, f (x i)) ≤ (n : ℝ)*q}) atTop (𝓝 0) := by
  let C := (∫ x, ‖f x-(∫ y, f y ∂μ)‖^2 ∂μ)/(∫ y, f y ∂μ-q)^2
  have ht : Tendsto (fun n : ℕ => C/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ ht
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact iid_sum_lower_probability_le μ f hf q hq n (by omega)

#print axioms iid_sum_lower_probability_le
#print axioms iid_sum_lower_probability_tendsto
end SpectralRadiusUpperTail
