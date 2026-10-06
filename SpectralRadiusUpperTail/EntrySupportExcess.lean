import SpectralRadiusUpperTail.IidSignedMultiplicityExcess
import SpectralRadiusUpperTail.IidWordSupport

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {σ τ 𝕂 : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]

lemma entryMultiplicity_used_sum (e : τ → σ) :
    (∑ i, if 0 < entryMultiplicity e i then 2 else 0) =
      2 * (Finset.univ.image e).card := by
  classical
  have hs : Finset.univ.filter (fun i => 0 < entryMultiplicity e i) = Finset.univ.image e := by
    ext i
    simp [entryMultiplicity_pos_iff]
  rw [← Finset.sum_filter, hs]
  simp [Nat.mul_comm]

lemma iidSignedWord_support_excess [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
    (μ : Measure 𝕂) [IsProbabilityMeasure μ] (hm : (∫ z : 𝕂, z ∂μ) = 0)
    (e : τ → σ) (s : τ → Bool)
    (hn : (∫ x : σ → 𝕂, (∏ t, if s t then star (x (e t)) else x (e t))
      ∂Measure.pi (fun _ : σ => μ)) ≠ 0) :
    Fintype.card τ = 2*(Finset.univ.image e).card + ∑ i, (entryMultiplicity e i-2) := by
  rw [iidSignedWord_excess_split μ hm e s hn, entryMultiplicity_used_sum]

/-- Multiplicity excess is at most twice the loss of vertices from the tree bound. -/
lemma excess_le_twice_vertex_defect (r E V δ : ℕ)
    (hlen : 2*r = 2*E+δ) (hvert : V ≤ E+1) : δ ≤ 2*(r+1-V) := by
  omega

#print axioms entryMultiplicity_used_sum
#print axioms iidSignedWord_support_excess
#print axioms excess_le_twice_vertex_defect
end SpectralRadiusUpperTail
