import SpectralRadiusUpperTail.RealSchurInvariantQuotientRank
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- If `P ≤ T`, the orthogonal part of `T` after `P` is exactly
`T ∩ Pᗮ`; it spans `T` together with `P`. -/
theorem realSchur_orthogonal_increment_sup
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (P T : Submodule ℝ E) (hPT : P ≤ T) :
    P ⊔ (T ⊓ Pᗮ) = T := by
  apply le_antisymm
  · exact sup_le hPT inf_le_left
  · intro x hx
    have hrest : ((Pᗮ).orthogonalProjectionOnto x : E) =
        x - (P.orthogonalProjectionOnto x : E) := by
      rw [P.orthogonalProjectionOnto_orthogonal]
      rfl
    have hp : (P.orthogonalProjectionOnto x : E) ∈ P :=
      (P.orthogonalProjectionOnto x).property
    have hq : ((Pᗮ).orthogonalProjectionOnto x : E) ∈ T ⊓ Pᗮ := by
      constructor
      · rw [hrest]
        exact T.sub_mem hx (hPT hp)
      · exact ((Pᗮ).orthogonalProjectionOnto x).property
    have hdecomp : x = (P.orthogonalProjectionOnto x : E) +
        ((Pᗮ).orthogonalProjectionOnto x : E) := by
      rw [hrest]
      abel
    rw [hdecomp]
    exact Submodule.add_mem_sup hp hq

/-- The orthogonal increment has the expected rank. -/
theorem realSchur_finrank_orthogonal_increment
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (P T : Submodule ℝ E) (hPT : P ≤ T) :
    Module.finrank ℝ ↥(T ⊓ Pᗮ) + Module.finrank ℝ P =
      Module.finrank ℝ T := by
  have hsup := realSchur_orthogonal_increment_sup P T hPT
  have hinf : P ⊓ (T ⊓ Pᗮ) = ⊥ := by
    apply eq_bot_iff.mpr
    calc
      P ⊓ (T ⊓ Pᗮ) ≤ P ⊓ Pᗮ := inf_le_inf le_rfl inf_le_right
      _ = ⊥ := P.inf_orthogonal_eq_bot
  have hdim := P.finrank_sup_add_finrank_inf_eq (T ⊓ Pᗮ)
  rw [hsup, hinf] at hdim
  simp at hdim
  omega

/-- A quotient block of rank one or two becomes an orthogonal
increment of the same rank in the original space. -/
theorem realSchur_finrank_orthogonal_quotient_increment
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (P : Submodule ℝ E) (Q : Submodule ℝ (E ⧸ P)) :
    Module.finrank ℝ ↥((Q.comap P.mkQ) ⊓ Pᗮ) = Module.finrank ℝ Q := by
  have hstep := realSchur_finrank_orthogonal_increment P (Q.comap P.mkQ)
    (Submodule.le_comap_mkQ P Q)
  rw [realSchur_finrank_comap_mkQ] at hstep
  omega

#print axioms realSchur_finrank_orthogonal_quotient_increment
end SpectralRadiusUpperTail
