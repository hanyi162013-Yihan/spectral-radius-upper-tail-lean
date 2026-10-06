import SpectralRadiusUpperTail.IidSignedTraceIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix
variable {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕂]
  [MeasurableSpace 𝕂] [BorelSpace 𝕂]

lemma gramTrace_eq_signed_trace (A : Matrix ι ι 𝕂) (m q : ℕ) :
    ((A^m * (A^m)ᴴ)^q).trace =
      ((gramSignWord m q).map (signedMatrixFactor A)).prod.trace := by
  rw [matrixGramWord_eq_signed, matrixGramWord_prod]

lemma iidGramTrace_integrable (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ) (m q : ℕ) :
    Integrable (fun x : ι × ι → 𝕂 =>
      (((Matrix.of (fun i j => x (i,j)))^m *
        ((Matrix.of (fun i j => x (i,j)))^m)ᴴ)^q).trace)
      (Measure.pi (fun _ : ι × ι => μ)) := by
  simp_rw [gramTrace_eq_signed_trace]
  exact iidSignedTrace_integrable μ c hc hexp _

lemma iidGramTraceMoment_integrable (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ) (m q : ℕ) :
    Integrable (fun x : ι × ι → 𝕂 =>
      matrixTraceMoment q ((Matrix.of (fun i j => x (i,j)))^m))
      (Measure.pi (fun _ : ι × ι => μ)) :=
  (iidGramTrace_integrable μ c hc hexp m q).re

lemma iidGramTraceMoment_eq_signed_integral (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ) (m q : ℕ) :
    (∫ x : ι × ι → 𝕂, matrixTraceMoment q ((Matrix.of (fun i j => x (i,j)))^m)
      ∂Measure.pi (fun _ : ι × ι => μ)) =
    RCLike.re (∫ x : ι × ι → 𝕂,
      ((gramSignWord m q).map (signedMatrixFactor (Matrix.of (fun i j => x (i,j))))).prod.trace
      ∂Measure.pi (fun _ : ι × ι => μ)) := by
  unfold matrixTraceMoment
  rw [integral_re (iidGramTrace_integrable μ c hc hexp m q)]
  simp_rw [gramTrace_eq_signed_trace]

#print axioms gramTrace_eq_signed_trace
#print axioms iidGramTrace_integrable
#print axioms iidGramTraceMoment_integrable
#print axioms iidGramTraceMoment_eq_signed_integral
end SpectralRadiusUpperTail
