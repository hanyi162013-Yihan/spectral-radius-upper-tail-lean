import SpectralRadiusUpperTail.OrientedSegmentChain
import SpectralRadiusUpperTail.SegmentEndpointParity

namespace SpectralRadiusUpperTail
variable {σ V : Type*}

/-- Each crossing toggles a Boolean cut color; only the outer endpoint colors
can contribute odd parity. -/
lemma OrientedSegmentChain.cut_crossing_boundary_even {ends : σ → V × V} {a b : V}
    {L : List (σ × Bool)} (h : OrientedSegmentChain ends a b L) (color : V → Bool) :
    Even ((L.filter (fun t => decide
      (color (segmentTokenStart ends t) ≠ color (segmentTokenFinish ends t)))).length +
        (if color a then 1 else 0) + (if color b then 1 else 0)) := by
  induction h with
  | nil a =>
    refine ⟨if color a then 1 else 0,?_⟩
    simp
  | cons t h ih =>
    rw [even_iff_two_dvd,Nat.dvd_iff_mod_eq_zero] at ih ⊢
    cases hs : color (segmentTokenStart ends t) <;>
      cases hf : color (segmentTokenFinish ends t) <;>
      simp [hs,hf] at ih ⊢ <;> omega

lemma OrientedSegmentChain.closed_cut_crossing_even {ends : σ → V × V} {a : V}
    {L : List (σ × Bool)} (h : OrientedSegmentChain ends a a L) (color : V → Bool) :
    Even ((L.filter (fun t => decide
      (color (segmentTokenStart ends t) ≠ color (segmentTokenFinish ends t)))).length) := by
  have hh := h.cut_crossing_boundary_even color
  rw [even_iff_two_dvd,Nat.dvd_iff_mod_eq_zero] at hh ⊢
  cases ha : color a <;> simp [ha] at hh ⊢ <;> omega

#print axioms OrientedSegmentChain.cut_crossing_boundary_even
#print axioms OrientedSegmentChain.closed_cut_crossing_even
end SpectralRadiusUpperTail
