import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

lemma norm_average_sq_le {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}
    (hn : 0 < n) (a : Fin n → 𝕂) :
    ‖(n : 𝕂)⁻¹ * ∑ i, a i‖^2 ≤ (∑ i, ‖a i‖^2)/(n : ℝ) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsum := norm_sum_le Finset.univ a
  have hsq : ‖∑ i, a i‖^2 ≤ (∑ i, ‖a i‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr hsum
  have hc : (∑ i, ‖a i‖)^2 ≤ (n : ℝ) * ∑ i, ‖a i‖^2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖a i‖))
  rw [norm_mul, norm_inv, RCLike.norm_natCast, mul_pow, inv_pow]
  calc
    _ ≤ ((n : ℝ)^2)⁻¹ * ((n : ℝ) * ∑ i, ‖a i‖^2) :=
      mul_le_mul_of_nonneg_left (hsq.trans hc) (by positivity)
    _ = _ := by field_simp

lemma integral_average_sq_le {Ω 𝕂 : Type*} [MeasurableSpace Ω] [RCLike 𝕂]
    {n : ℕ} (hn : 0 < n) (μ : Measure Ω) (f : Fin n → Ω → 𝕂)
    (hi : ∀ i, Integrable (fun x => ‖f i x‖^2) μ)
    (hm : AEStronglyMeasurable (fun x => ‖(n : 𝕂)⁻¹ * ∑ i, f i x‖^2) μ)
    (B : ℝ) (hB : ∀ i, (∫ x, ‖f i x‖^2 ∂μ) ≤ B) :
    Integrable (fun x => ‖(n : 𝕂)⁻¹ * ∑ i, f i x‖^2) μ ∧
      (∫ x, ‖(n : 𝕂)⁻¹ * ∑ i, f i x‖^2 ∂μ) ≤ B := by
  have hdom : Integrable (fun x => (∑ i, ‖f i x‖^2)/(n : ℝ)) μ :=
    (integrable_finsetSum _ (fun i _ => hi i)).div_const _
  have hsmall : Integrable (fun x => ‖(n : 𝕂)⁻¹ * ∑ i, f i x‖^2) μ := by
    apply hdom.mono' hm
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact norm_average_sq_le hn (fun i => f i x)
  refine ⟨hsmall, (integral_mono hsmall hdom (fun x => norm_average_sq_le hn _)).trans ?_⟩
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const, integral_finsetSum _ (fun i _ => hi i)]
  rw [← div_eq_mul_inv]
  have hs : (∑ i, ∫ x, ‖f i x‖^2 ∂μ) ≤ (n : ℝ)*B := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hB i)
  exact (div_le_iff₀ (Nat.cast_pos.mpr hn)).mpr (by simpa only [mul_comm] using hs)

#print axioms norm_average_sq_le
#print axioms integral_average_sq_le
end SpectralRadiusUpperTail
