import SpectralRadiusUpperTail.RealSchurMixedCodeClassConnected
import Mathlib.Analysis.Convex.Topology

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

theorem realSchurMixedUpperEntryJoin_continuous
    {m : ℕ} (s : Fin m → ℕ) :
    Continuous (fun z : (RealSchurMixedDiagonalEntry s → ℝ) ×
      (RealSchurMixedStrictUpperEntry s → ℝ) => realSchurMixedUpperEntryJoin s z.1 z.2) := by
  apply continuous_matrix
  intro i j
  unfold realSchurMixedUpperEntryJoin
  split_ifs <;> fun_prop

/-- Every realized code, not only the code of the displayed Schur
representation, is unchanged when the strictly-upper entries vary. -/
theorem realSchurMixedCodeClass_upper_fiber_iff
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, s i=1 ∨ s i=2)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (d : RealSchurMixedDiagonalEntry s → ℝ)
    (u v : RealSchurMixedStrictUpperEntry s → ℝ)
    (hsep : (realSchurMixedUpperEntryJoin s d u).charpoly.Separable) :
    realSchurMixedUpperEntryJoin s d u ∈ realSchurMixedCodeClass s code ↔
      realSchurMixedUpperEntryJoin s d v ∈ realSchurMixedCodeClass s code := by
  have hspos : ∀ i, 0 < s i := by
    intro i
    rcases hs i with h | h <;> omega
  apply realSchurMixedCodeClass_connected_iff s hs code
    (fun w => realSchurMixedUpperEntryJoin s d w)
  · exact (realSchurMixedUpperEntryJoin_continuous s).comp (continuous_const.prodMk continuous_id)
  · intro w
    exact (realSchurMixedUpperEntryJoin_charpoly_fiber_const s hspos d u w) ▸ hsep
  · intro w z
    exact realSchurMixedUpperEntryJoin_charpoly_fiber_const s hspos d w z

#print axioms realSchurMixedUpperEntryJoin_continuous
#print axioms realSchurMixedCodeClass_upper_fiber_iff
end SpectralRadiusUpperTail
