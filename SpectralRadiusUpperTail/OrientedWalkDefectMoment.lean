import SpectralRadiusUpperTail.EntrySupportExcess
import SpectralRadiusUpperTail.SignedWalkSupport
import SpectralRadiusUpperTail.IidSignedExcessMoment

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {ι 𝕂 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕂]
  [MeasurableSpace 𝕂] [BorelSpace 𝕂] {r : ℕ}

lemma orientedWalk_nonzero_excess_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (hm : (∫ z : 𝕂, z ∂μ) = 0)
    (s : Fin (2*r) → Bool) (v : Fin (2*r+1) → ι) (hcover : Function.Surjective v)
    (hn : (∫ x : ι × ι → 𝕂, (∏ a, if s a then star (x (orientedWalkEdge s v a))
      else x (orientedWalkEdge s v a)) ∂Measure.pi (fun _ : ι × ι => μ)) ≠ 0) :
    (∑ e : ι × ι, (entryMultiplicity (orientedWalkEdge s v) e-2)) ≤
      2*(r+1-Fintype.card ι) := by
  have hlen := iidSignedWord_support_excess μ hm (orientedWalkEdge s v) s hn
  simp only [Fintype.card_fin] at hlen
  exact excess_le_twice_vertex_defect _ _ _ _ hlen (orientedWalk_vertex_card_le s v hcover)

/-- Actual iid moment cost of a covered oriented path, controlled by vertex deficit. -/
lemma orientedWalk_vertex_defect_moment_le (μ : Measure 𝕂) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hexp : Integrable (fun z : 𝕂 => Real.exp (c*‖z‖^2)) μ)
    (hm : (∫ z : 𝕂, z ∂μ) = 0) (hv : (∫ z : 𝕂, ‖z‖^2 ∂μ) = 1)
    (s : Fin (2*r) → Bool) (v : Fin (2*r+1) → ι) (hcover : Function.Surjective v) :
    ‖∫ x : ι × ι → 𝕂, (∏ a, if s a then star (x (orientedWalkEdge s v a))
      else x (orientedWalkEdge s v a)) ∂Measure.pi (fun _ : ι × ι => μ)‖ ≤
      (signedWordMomentBase μ c (2*r))^(6*(r+1-Fintype.card ι)) := by
  have hB := signedWordMomentBase_one_le μ c hc (2*r)
  by_cases hz : (∫ x : ι × ι → 𝕂, (∏ a, if s a then star (x (orientedWalkEdge s v a))
      else x (orientedWalkEdge s v a)) ∂Measure.pi (fun _ : ι × ι => μ)) = 0
  · rw [hz,norm_zero]
    exact pow_nonneg (le_trans (by norm_num) hB) _
  have h := iidSignedWord_excess_moment_bound μ c hc hexp hm hv (orientedWalkEdge s v) s
  simp only [Fintype.card_fin] at h
  apply h.trans
  apply pow_le_pow_right₀ hB
  have he := orientedWalk_nonzero_excess_le μ hm s v hcover hz
  omega

#print axioms orientedWalk_nonzero_excess_le
#print axioms orientedWalk_vertex_defect_moment_le
end SpectralRadiusUpperTail
