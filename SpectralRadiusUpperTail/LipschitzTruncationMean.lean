import SpectralRadiusUpperTail.ProductDiscardedEnergy
import SpectralRadiusUpperTail.ArrayTruncationEnergy

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp Filter
open scoped BigOperators NNReal Topology
variable {𝕂 : Type*} [RCLike 𝕂]

lemma lipschitz_truncation_mean_bound (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (R : ℝ) (L : ℝ≥0)
    (hi : Integrable (fun x : 𝕂 => ‖x‖^2) μ)
    (f : EuclideanSpace 𝕂 (Fin (n*n)) → ℝ) (hf : LipschitzWith (L/(n : ℝ≥0)) f) :
    Integrable (fun x : Fin (n*n) → 𝕂 =>
      |f (toLp 2 x)-f (toLp 2 (fun i => entryCutoff R (x i)))|) (Measure.pi (fun _ => μ)) ∧
    (∫ x : Fin (n*n) → 𝕂, |f (toLp 2 x)-f (toLp 2 (fun i => entryCutoff R (x i)))|
      ∂Measure.pi (fun _ => μ)) ≤ (L : ℝ)*Real.sqrt (∫ x, discardedSquare R x ∂μ) := by
  letI : MeasurableSpace (EuclideanSpace 𝕂 (Fin (n*n))) := borel _
  letI : BorelSpace (EuclideanSpace 𝕂 (Fin (n*n))) := ⟨rfl⟩
  have hs := product_discarded_energy_sqrt μ (n*n) R hi
  have hmcut : Measurable (fun x : Fin (n*n) → 𝕂 => fun i => entryCutoff R (x i)) :=
    measurable_pi_lambda _ (fun i => (entryCutoff_measurable R).comp (measurable_pi_apply i))
  have hmlp : Measurable (fun x : Fin (n*n) → 𝕂 => toLp 2 x) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin (n*n) => 𝕂)).measurable
  have hm : Measurable (fun x : Fin (n*n) → 𝕂 =>
      |f (toLp 2 x)-f (toLp 2 (fun i => entryCutoff R (x i)))|) := by
    have hd : Measurable (fun x : Fin (n*n) → 𝕂 =>
        f (toLp 2 x)-f (toLp 2 (fun i => entryCutoff R (x i)))) :=
      (hf.continuous.measurable.comp hmlp).sub (hf.continuous.measurable.comp (hmlp.comp hmcut))
    simpa only [Real.norm_eq_abs] using hd.norm
  have hb (x : Fin (n*n) → 𝕂) :
      |f (toLp 2 x)-f (toLp 2 (fun i => entryCutoff R (x i)))| ≤
        ((L : ℝ)/(n : ℝ))*Real.sqrt (∑ i, discardedSquare R (x i)) := by
    simpa only [NNReal.coe_div,NNReal.coe_natCast] using
      arrayCutoff_lipschitz_error (n*n) R (L/(n : ℝ≥0)) f hf x
  have hierr : Integrable (fun x : Fin (n*n) → 𝕂 =>
      |f (toLp 2 x)-f (toLp 2 (fun i => entryCutoff R (x i)))|) (Measure.pi (fun _ => μ)) := by
    apply (hs.1.const_mul ((L : ℝ)/(n : ℝ))).mono' hm.aestronglyMeasurable
    filter_upwards with x
    simpa only [Real.norm_eq_abs,abs_abs] using hb x
  refine ⟨hierr,?_⟩
  have hbound := (integral_mono hierr (hs.1.const_mul ((L : ℝ)/(n : ℝ))) hb)
  rw [integral_const_mul] at hbound
  apply hbound.trans
  have hh := mul_le_mul_of_nonneg_left hs.2 (show 0 ≤ (L : ℝ)/(n : ℝ) by positivity)
  have hq : 0 ≤ ∫ x, discardedSquare R x ∂μ := integral_nonneg (fun x => (discardedSquare_bounds R x).1)
  rw [Nat.cast_mul,show (n : ℝ)*(n : ℝ) = (n : ℝ)^2 from (pow_two _).symm,Real.sqrt_mul (sq_nonneg (n : ℝ)),Real.sqrt_sq (Nat.cast_nonneg n)] at hh
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  convert! hh using 1
  field_simp
  <;> ring

lemma lipschitz_truncation_mean_uniform (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) (hi : Integrable (fun x : 𝕂 => ‖x‖^2) μ) :
    ∀ᶠ K : ℕ in atTop, ∀ n : ℕ, 0 < n → ∀ f : EuclideanSpace 𝕂 (Fin (n*n)) → ℝ,
      LipschitzWith (L/(n : ℝ≥0)) f →
      (∫ x : Fin (n*n) → 𝕂, |f (toLp 2 x)-f (toLp 2 (fun i => entryCutoff (K : ℝ) (x i)))|
        ∂Measure.pi (fun _ => μ)) ≤ δ := by
  have ht := (discardedSquare_mean_tendsto_zero μ hi).sqrt.const_mul (L : ℝ)
  have hsmall : ∀ᶠ K : ℕ in atTop,
      (L : ℝ)*Real.sqrt (∫ x, discardedSquare (K : ℝ) x ∂μ) < δ := by
    apply (tendsto_order.1 (show Tendsto _ atTop (𝓝 (0 : ℝ)) from by simpa using ht)).2 δ hδ
  filter_upwards [hsmall] with K hK
  intro n hn f hf
  exact (lipschitz_truncation_mean_bound μ n hn (K : ℝ) L hi f hf).2.trans hK.le

#print axioms lipschitz_truncation_mean_bound
#print axioms lipschitz_truncation_mean_uniform
end SpectralRadiusUpperTail
