import SpectralRadiusUpperTail.ConvexConcentrationFromCutoffs

namespace SpectralRadiusUpperTail
open MeasureTheory Filter WithLp
open scoped Topology NNReal
variable {𝕂 : Type*} [RCLike 𝕂]

/-- Explicit remaining input: uniform centered convex concentration for every
fixed bounded cutoff of the iid entry law. No theorem or axiom is asserted here. -/
def CutoffConvexConcentration (μ : Measure 𝕂) : Prop :=
  ∀ (K : ℕ) (L : ℝ≥0) (δ : ℝ), 0 < (L : ℝ) → 0 < δ →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ q : ℝ, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
        ∀ f : EuclideanSpace 𝕂 (Fin (n*n)) → ℝ,
          ConvexOn ℝ Set.univ f → LipschitzWith (L/(n : ℝ≥0)) f →
          (Measure.pi (fun _ : Fin (n*n) => μ.map (entryCutoff (K : ℝ)))).real
            {x | δ < |f (toLp 2 x)-(∫ y : Fin (n*n) → 𝕂, f (toLp 2 y)
              ∂Measure.pi (fun _ => μ.map (entryCutoff (K : ℝ))))|} ≤ C*Real.exp (-q*(n : ℝ)^2)

/-- Uniform centered concentration for convex L/n-Lipschitz observables. -/
def IidConvexConcentration (μ : Measure 𝕂) : Prop :=
  ∀ (L : ℝ≥0) (δ : ℝ), 0 < (L : ℝ) → 0 < δ →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ q : ℝ, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
        ∀ f : EuclideanSpace 𝕂 (Fin (n*n)) → ℝ,
          ConvexOn ℝ Set.univ f → LipschitzWith (L/(n : ℝ≥0)) f →
          (Measure.pi (fun _ : Fin (n*n) => μ)).real
            {x | δ < |f (toLp 2 x)-(∫ y : Fin (n*n) → 𝕂, f (toLp 2 y)
              ∂Measure.pi (fun _ => μ))|} ≤ C*Real.exp (-q*(n : ℝ)^2)

lemma cutoff_concentration_transfer (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun x : 𝕂 => Real.exp (c*‖x‖^2)) μ)
    (h2 : Integrable (fun x : 𝕂 => ‖x‖^2) μ)
    (hcut : CutoffConvexConcentration μ) : IidConvexConcentration μ :=
  convex_concentration_of_cutoff_laws μ c hc hexp h2 hcut

#print axioms cutoff_concentration_transfer
end SpectralRadiusUpperTail
