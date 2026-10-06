import SpectralRadiusUpperTail.IidEmbeddingIntegral
import SpectralRadiusUpperTail.IidWordMoments
import SpectralRadiusUpperTail.GaussianMoments

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

lemma iid_real_word_pair_integrable {σ τ υ : Type*} [Fintype σ] [DecidableEq σ]
    [Fintype τ] [Fintype υ] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : ∀ k : ℕ, Integrable (fun x : ℝ => x^k) μ) (e : τ → σ) (f : υ → σ) :
    Integrable (fun x : σ → ℝ => (∏ j, x (e j))*(∏ j, x (f j))) (Measure.pi (fun _ => μ)) := by
  simp_rw [entryWord_product_eq_powers, ← Finset.prod_mul_distrib, ← pow_add]
  exact Integrable.fintype_prod (fun i => hi (entryMultiplicity e i+entryMultiplicity f i))

/-- An injective word uses each centered edge once. Its diagonal second
moment factors over the edges themselves, even if other paths share them. -/
lemma iid_simple_word_second_moment {σ τ : Type*} [Fintype σ] [Fintype τ]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (e : τ → σ) (he : Function.Injective e) :
    (∫ x : σ → ℝ, (∏ j, x (e j))^2 ∂Measure.pi (fun _ => μ)) =
      (∫ z : ℝ, z^2 ∂μ)^(Fintype.card τ) := by
  rw [iidIndexEmbedding_integral μ e he (fun y : τ → ℝ => (∏ j, y j)^2) (by fun_prop)]
  simp_rw [← Finset.prod_pow]
  exact integral_fintype_prod_eq_pow (μ := μ) (fun z : ℝ => z^2)

lemma gaussian_simple_word_second_moment {σ : Type*} [Fintype σ]
    {k : ℕ} (e : Fin k → σ) (he : Function.Injective e) :
    (∫ x : σ → ℝ, (∏ j, x (e j))^2 ∂Measure.pi (fun _ => standardNormal)) = 1 := by
  rw [iid_simple_word_second_moment standardNormal e he, standardNormal_second_moment, one_pow]

lemma gaussian_scaled_simple_word_second_moment {σ : Type*} [Fintype σ]
    {k : ℕ} (e : Fin k → σ) (he : Function.Injective e) (n : ℕ) (hn : 0 < n) :
    (∫ x : σ → ℝ, (∏ j, x (e j)/Real.sqrt n)^2
      ∂Measure.pi (fun _ => standardNormal)) = (1/(n : ℝ))^k := by
  simp_rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, div_pow]
  rw [integral_div, gaussian_simple_word_second_moment e he]
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [← pow_mul, Nat.mul_comm k 2, pow_mul, Real.sq_sqrt hnR]
  simp

#print axioms iid_real_word_pair_integrable
#print axioms gaussian_scaled_simple_word_second_moment
end SpectralRadiusUpperTail
