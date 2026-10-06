import SpectralRadiusUpperTail.SignedTracePatternBound
import SpectralRadiusUpperTail.IidGramTraceIntegral
import SpectralRadiusUpperTail.GramPatternGeometricBound

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕂]
  [MeasurableSpace 𝕂] [BorelSpace 𝕂]

lemma gramSignWord_get_cast (m q : ℕ)
    (h : (gramSignWord m q).length = 2*(q*m)) (a : Fin (2*(q*m))) :
    (gramSignWord m q).get (Fin.cast h.symm a) = gramTreeSign m q a := by
  unfold gramTreeSign
  rw [gramFiniteSign_eq_getElem]
  rfl

lemma iidGramTraceMoment_le_pattern_sum (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (m q : ℕ) :
    (∫ x : ι × ι → 𝕂, matrixTraceMoment q ((Matrix.of (fun i j => x (i,j)))^m)
      ∂Measure.pi (fun _ : ι × ι => μ)) ≤
    ∑ R : Setoid (Fin (2*(q*m)+1)),
      closedPatternWeight μ (gramTreeSign m q) (Fintype.card ι) R := by
  rw [iidGramTraceMoment_eq_signed_integral μ c hc hexp m q]
  apply (RCLike.re_le_norm _).trans
  have hl : (gramSignWord m q).length = 2*(q*m) :=
    (gramSignWord_length m q).trans (Nat.mul_assoc 2 q m)
  have hh := signedTrace_integral_norm_le_patterns (ι := ι) μ c hc hexp (gramSignWord m q) hl
  have hs : (fun a => (gramSignWord m q).get (Fin.cast hl.symm a)) = gramTreeSign m q := by
    funext a
    exact gramSignWord_get_cast m q hl a
  rw [hs] at hh
  exact hh

lemma iidGramTraceMoment_le_two (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c) (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (hv : (∫ z : 𝕂, ‖z‖^2 ∂μ) = 1)
    (m q : ℕ) (hq : 1 ≤ q) (hn : 0 < Fintype.card ι)
    (hr : gramDefectRatio μ c m q (Fintype.card ι) ≤ 1/2) :
    (∫ x : ι × ι → 𝕂, matrixTraceMoment q ((Matrix.of (fun i j => x (i,j)))^m)
      ∂Measure.pi (fun _ : ι × ι => μ)) ≤
    2*(m+1 : ℝ)^(2*q) * (Fintype.card ι : ℝ)^(q*m+1) :=
  (iidGramTraceMoment_le_pattern_sum μ c hc hexp m q).trans
    (gramPatternWeight_sum_le_two μ c hc hexp hm hv m q _ hq hn hr)

#print axioms gramSignWord_get_cast
#print axioms iidGramTraceMoment_le_pattern_sum
#print axioms iidGramTraceMoment_le_two
end SpectralRadiusUpperTail
