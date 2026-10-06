import SpectralRadiusUpperTail.GaussianReplacement

namespace SpectralRadiusUpperTail
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [SecondCountableTopology E]

lemma hilbert_projection_product_integrable (μ : Measure E)
    (hX : MemLp (fun x : E => x) 2 μ) (s w : E) :
    Integrable (fun x : E => inner ℝ s x*inner ℝ w x) μ := by
  have hs : MemLp (fun x : E => inner ℝ s x) 2 μ := hX.const_inner s
  have hw : MemLp (fun x : E => inner ℝ w x) 2 μ := hX.const_inner w
  exact hs.integrable_mul hw

/-- Polarization recovers all mixed second moments from the projection squares. -/
lemma hilbert_projection_product_integral (μ : Measure E)
    (hX : MemLp (fun x : E => x) 2 μ) (s w : E) :
    (∫ x : E, inner ℝ s x*inner ℝ w x ∂μ) =
      (((∫ x : E, (inner ℝ (s+w) x)^2 ∂μ)-
        (∫ x : E, (inner ℝ s x)^2 ∂μ))-(∫ x : E, (inner ℝ w x)^2 ∂μ))/2 := by
  have he (x : E) : inner ℝ s x*inner ℝ w x =
      (((inner ℝ (s+w) x)^2-(inner ℝ s x)^2)-(inner ℝ w x)^2)/2 := by
    rw [inner_add_left]
    ring
  simp_rw [he]
  rw [integral_div, integral_sub, integral_sub]
  all_goals first | exact hilbert_projection_square_integrable μ hX _ |
    exact (hilbert_projection_square_integrable μ hX _).sub
      (hilbert_projection_square_integrable μ hX _)

lemma hilbert_projection_product_matching (μ ν : Measure E)
    (hXμ : MemLp (fun x : E => x) 2 μ) (hXν : MemLp (fun x : E => x) 2 ν)
    (hcov : ∀ s : E, (∫ x : E, (inner ℝ s x)^2 ∂μ) = ∫ x : E, (inner ℝ s x)^2 ∂ν)
    (s w : E) :
    (∫ x : E, inner ℝ s x*inner ℝ w x ∂μ) = ∫ x : E, inner ℝ s x*inner ℝ w x ∂ν := by
  rw [hilbert_projection_product_integral μ hXμ, hilbert_projection_product_integral ν hXν,
    hcov (s+w), hcov s, hcov w]

#print axioms hilbert_projection_product_matching
end SpectralRadiusUpperTail
