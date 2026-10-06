import SpectralRadiusUpperTail.RealSchurInvariantQuotient
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- An invariant subspace with a nonzero quotient can be enlarged by
the pullback of a one- or two-dimensional invariant quotient subspace.
This is the algebraic recursive step behind global real Schur form. -/
theorem realLinearMap_invariant_subspace_strict_extension
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (P : Submodule ℝ E)
    (hP : ∀ x ∈ P, f x ∈ P)
    (hquot : 0 < Module.finrank ℝ (E ⧸ P)) :
    ∃ Q : Submodule ℝ (E ⧸ P),
      (Module.finrank ℝ Q = 1 ∨ Module.finrank ℝ Q = 2) ∧
      P < Q.comap P.mkQ ∧
      ∀ x ∈ Q.comap P.mkQ, f x ∈ Q.comap P.mkQ := by
  obtain ⟨Q,hRank,hInv⟩ :=
    realLinearMap_exists_invariant_subspace_rank_one_or_two hquot
      (realLinearMapInvariantQuotient f P hP)
  have hQne : Q ≠ ⊥ := by
    intro hQ
    subst Q
    rcases hRank with hRank | hRank <;> simp at hRank
  have hmapP : P.map P.mkQ = ⊥ := by
    apply eq_bot_iff.mpr
    rw [Submodule.map_le_iff_le_comap]
    simp
  have hstrict : P < Q.comap P.mkQ := by
    apply lt_of_le_of_ne (Submodule.le_comap_mkQ P Q)
    intro heq
    apply hQne
    calc
      Q = (Q.comap P.mkQ).map P.mkQ :=
        (Submodule.map_comap_eq_self (by simp)).symm
      _ = P.map P.mkQ := by rw [← heq]
      _ = ⊥ := hmapP
  exact ⟨Q,hRank,hstrict,
    realLinearMapInvariantQuotient_comap_invariant f P hP Q hInv⟩

#print axioms realLinearMap_invariant_subspace_strict_extension
end SpectralRadiusUpperTail
