import SpectralRadiusUpperTail.DiscardedSquareChernoff
import SpectralRadiusUpperTail.ArrayTruncationEnergy

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp Filter
open scoped BigOperators NNReal
variable {𝕂 : Type*} [RCLike 𝕂]

lemma lipschitz_truncation_tail_of_logmgf (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c δ : ℝ) (L : ℝ≥0) (hc : 0 < c) (hδ : 0 < δ) (hL : 0 < (L : ℝ))
    (hi : Integrable (fun x : 𝕂 => Real.exp (c*‖x‖^2)) μ) (K : ℕ)
    (hlog : Real.log (∫ x, Real.exp (c*discardedSquare (K : ℝ) x) ∂μ) ≤ c*(δ/(L : ℝ))^2/2)
    (n : ℕ) (hn : 0 < n) (f : EuclideanSpace 𝕂 (Fin (n*n)) → ℝ)
    (hf : LipschitzWith (L/(n : ℝ≥0)) f) :
    (Measure.pi (fun _ : Fin (n*n) => μ)).real
      {x | δ < |f (toLp 2 x)-f (toLp 2 (fun i => entryCutoff (K : ℝ) (x i)))|} ≤
        Real.exp (-c*(δ/(L : ℝ))^2*(n : ℝ)^2/2) := by
  have hKn : (Measure.pi (fun _ : Fin (n*n) => μ)).real
      {x | (n : ℝ)^2*(δ/(L : ℝ))^2 ≤ ∑ i, discardedSquare (K : ℝ) (x i)} ≤
        Real.exp (-c*(δ/(L : ℝ))^2*(n : ℝ)^2/2) := by
    simpa only [Nat.cast_mul,pow_two] using
      iid_exponential_sum_tail μ (discardedSquare (K : ℝ)) c ((δ/(L : ℝ))^2) hc
        (discardedSquare_exp_integrable μ c (K : ℝ) hc.le hi) hlog (n*n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (measureReal_mono (μ := Measure.pi (fun _ : Fin (n*n) => μ)) ?_).trans hKn
  intro x hx
  have hb := arrayCutoff_lipschitz_error (n*n) (K : ℝ) (L/(n : ℝ≥0)) f hf x
  simp only [NNReal.coe_div,NNReal.coe_natCast] at hb
  have hlt : δ/((L : ℝ)/(n : ℝ)) < Real.sqrt (∑ i, discardedSquare (K : ℝ) (x i)) :=
    (div_lt_iff₀ (div_pos hL hnR)).mpr (by simpa only [mul_comm] using hx.trans_le hb)
  have hs : 0 ≤ ∑ i, discardedSquare (K : ℝ) (x i) :=
    Finset.sum_nonneg (fun i _ => (discardedSquare_bounds (K : ℝ) (x i)).1)
  have hsq := (sq_lt_sq₀ (by positivity : 0 ≤ δ/((L : ℝ)/(n : ℝ))) (Real.sqrt_nonneg _)).mpr hlt
  rw [Real.sq_sqrt hs] at hsq
  have he : (δ/((L : ℝ)/(n : ℝ)))^2 = (n : ℝ)^2*(δ/(L : ℝ))^2 := by
    field_simp
    <;> ring
  change (n : ℝ)^2*(δ/(L : ℝ))^2 ≤ ∑ i, discardedSquare (K : ℝ) (x i)
  rw [he] at hsq
  exact hsq.le


/-- A fixed coordinate cutoff controls every L/n-Lipschitz observable at quadratic speed. -/
lemma lipschitz_truncation_quadratic_tail (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c δ : ℝ) (L : ℝ≥0) (hc : 0 < c) (hδ : 0 < δ) (hL : 0 < (L : ℝ))
    (hi : Integrable (fun x : 𝕂 => Real.exp (c*‖x‖^2)) μ) :
    ∃ K : ℕ, ∀ n : ℕ, 0 < n → ∀ f : EuclideanSpace 𝕂 (Fin (n*n)) → ℝ,
      LipschitzWith (L/(n : ℝ≥0)) f →
      (Measure.pi (fun _ : Fin (n*n) => μ)).real
        {x | δ < |f (toLp 2 x)-f (toLp 2 (fun i => entryCutoff (K : ℝ) (x i)))|} ≤
          Real.exp (-c*(δ/(L : ℝ))^2*(n : ℝ)^2/2) := by
  have he := (tendsto_order.1 (discardedSquare_log_mgf_tendsto_zero μ c hi)).2
    (c*(δ/(L : ℝ))^2/2) (by positivity)
  obtain ⟨K,hK⟩ := he.exists
  refine ⟨K,fun n hn f hf => ?_⟩
  exact lipschitz_truncation_tail_of_logmgf μ c δ L hc hδ hL hi K hK.le n hn f hf

#print axioms lipschitz_truncation_tail_of_logmgf
#print axioms lipschitz_truncation_quadratic_tail
end SpectralRadiusUpperTail
