import SpectralRadiusUpperTail.KernelTruncation

namespace SpectralRadiusUpperTail
open MeasureTheory ProbabilityTheory
variable {Θ α E : Type*} [MeasurableSpace Θ] [MeasurableSpace α]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The actual conditional truncation has no larger variance; its squared
approximation error is bounded by the actual discarded conditional moment. -/
theorem kernelTruncated_conditional_moments (κ : Kernel Θ α) [IsMarkovKernel κ]
    (f : Θ × α → E) (hf : Measurable f) (s : Θ)
    (h1 : Integrable (fun x => f (s,x)) (κ s))
    (h2 : Integrable (fun x => ‖f (s,x)‖^2) (κ s))
    (hm : (∫ x, f (s,x) ∂κ s) = 0) (R : ℝ) (hR : 0 ≤ R) :
    (∫ x, ‖kernelCentered κ (kernelTruncated f R) (s,x)‖^2 ∂κ s) ≤
      ∫ x, ‖f (s,x)‖^2 ∂κ s ∧
      (∫ x, ‖f (s,x)-kernelCentered κ (kernelTruncated f R) (s,x)‖^2 ∂κ s) ≤
        ∫ x in {x | R < ‖f (s,x)‖}, ‖f (s,x)‖^2 ∂κ s := by
  have hh := recentered_truncation_moments (κ s) (fun x => f (s,x))
    (hf.comp (measurable_const.prodMk measurable_id)) h1 h2 hm R hR
  exact ⟨hh.2.2.2.1, hh.2.2.2.2⟩

/-- A conditional exponential-square moment gives a quantitative discarded
conditional second-moment bound for the actual recentered truncation. -/
theorem kernelTruncated_conditional_error (κ : Kernel Θ α) [IsMarkovKernel κ]
    (f : Θ × α → E) (hf : Measurable f) (s : Θ)
    (hm : (∫ x, f (s,x) ∂κ s) = 0) (c M R : ℝ) (hc : 0 < c) (hR : 0 ≤ R)
    (he : Integrable (fun x => Real.exp (c*‖f (s,x)‖^2)) (κ s))
    (hb : (∫ x, Real.exp (c*‖f (s,x)‖^2) ∂κ s) ≤ M) :
    (∫ x, ‖f (s,x)-kernelCentered κ (kernelTruncated f R) (s,x)‖^2 ∂κ s) ≤
      (2/c)*Real.exp (-(c/2)*R^2)*M := by
  have hfm : Measurable (fun x => f (s,x)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  obtain ⟨h1,h2⟩ := squareExp_moments (κ s) _ hfm.aestronglyMeasurable c hc he
  exact (kernelTruncated_conditional_moments κ f hf s h1 h2 hm R hR).2.trans
    (squareExp_tail_secondMoment (κ s) _ hfm c M R hc hR he hb)

#print axioms kernelTruncated_conditional_error
end SpectralRadiusUpperTail
