import SpectralRadiusUpperTail.IidGramTraceIntegral

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕂]
  [MeasurableSpace 𝕂] [BorelSpace 𝕂]

/-- The actual unnormalized iid Gram trace moment as a closed-path sum of scalar moments. -/
lemma iidGramTraceMoment_scalar_expansion (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ) (m q : ℕ) :
    (∫ x : ι × ι → 𝕂, matrixTraceMoment q ((Matrix.of (fun i j => x (i,j)))^m)
      ∂Measure.pi (fun _ : ι × ι => μ)) =
    let L := gramSignWord m q
    RCLike.re (∑ i, ∑ v : Fin L.length → ι,
      (∏ e : ι × ι, ∫ z : 𝕂,
        z^(entryMultiplicity (fun a => (signedWalkEdge L i v a,L.get a)) (e,false)) *
        (star z)^(entryMultiplicity (fun a => (signedWalkEdge L i v a,L.get a)) (e,true)) ∂μ) *
      (1 : Matrix ι ι 𝕂) ((Fin.cons i v : Fin (L.length+1) → ι) (Fin.last L.length)) i) := by
  rw [iidGramTraceMoment_eq_signed_integral μ c hc hexp m q,
    iidSignedTrace_integral μ c hc hexp (gramSignWord m q)]

#print axioms iidGramTraceMoment_scalar_expansion
end SpectralRadiusUpperTail
