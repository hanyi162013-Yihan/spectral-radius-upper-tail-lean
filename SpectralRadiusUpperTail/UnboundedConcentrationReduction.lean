import SpectralRadiusUpperTail.LipschitzTruncationTail
import SpectralRadiusUpperTail.LipschitzTruncationMean
import SpectralRadiusUpperTail.CenteredConcentrationTransfer
import SpectralRadiusUpperTail.EntryCutoffLaw

namespace SpectralRadiusUpperTail
open MeasureTheory WithLp Filter
open scoped BigOperators NNReal Topology
variable {𝕂 : Type*} [RCLike 𝕂]

/-- Fixed-cutoff reduction of concentration around the actual mean to the bounded-entry law. -/
lemma unbounded_concentration_reduction (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c δ : ℝ) (L : ℝ≥0) (hc : 0 < c) (hδ : 0 < δ) (hL : 0 < (L : ℝ))
    (hi : Integrable (fun x : 𝕂 => Real.exp (c*‖x‖^2)) μ)
    (h2 : Integrable (fun x : 𝕂 => ‖x‖^2) μ) :
    ∃ K : ℕ, ∃ q : ℝ, 0 < q ∧ ∀ n : ℕ, 0 < n →
      ∀ f : EuclideanSpace 𝕂 (Fin (n*n)) → ℝ, LipschitzWith (L/(n : ℝ≥0)) f →
      let P := Measure.pi (fun _ : Fin (n*n) => μ)
      let F := fun x : Fin (n*n) → 𝕂 => f (toLp 2 x)
      let G := fun x : Fin (n*n) → 𝕂 => f (toLp 2 (fun i => entryCutoff (K : ℝ) (x i)))
      Integrable F P → Integrable G P →
      P.real {x | δ < |F x-(∫ y, F y ∂P)|} ≤
        P.real {x | δ/2 < |G x-(∫ y, G y ∂P)|}+Real.exp (-q*(n : ℝ)^2) := by
  have hmean := lipschitz_truncation_mean_uniform μ L (δ/4) (by positivity) h2
  have hlog := (tendsto_order.1 (discardedSquare_log_mgf_tendsto_zero μ c hi)).2
    (c*((δ/4)/(L : ℝ))^2/2) (by positivity)
  obtain ⟨K,hKm,hKl⟩ := (hmean.and hlog).exists
  refine ⟨K,c*((δ/4)/(L : ℝ))^2/2,by positivity,?_⟩
  intro n hn f hf
  dsimp only
  intro hF hG
  have ht := centered_concentration_transfer_of_integral_error
    (Measure.pi (fun _ : Fin (n*n) => μ))
    (fun x : Fin (n*n) → 𝕂 => f (toLp 2 x))
    (fun x : Fin (n*n) → 𝕂 => f (toLp 2 (fun i => entryCutoff (K : ℝ) (x i))))
    hF hG δ (hKm n hn f hf)
  have he := lipschitz_truncation_tail_of_logmgf μ c (δ/4) L hc (by positivity) hL hi K hKl.le n hn f hf
  apply ht.trans
  refine add_le_add le_rfl ?_
  convert! he using 1
  congr 1
  ring

#print axioms unbounded_concentration_reduction
end SpectralRadiusUpperTail
