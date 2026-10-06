import SpectralRadiusUpperTail.RealSchurInvariantExtension
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- A finite invariant flag whose successive quotient blocks have real
dimension one or two. The terminal subspace is the whole space. -/
inductive RealSchurInvariantFlag
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E →ₗ[ℝ] E) : List (Submodule ℝ E) → Prop where
  | done : RealSchurInvariantFlag f [⊤]
  | step (P : Submodule ℝ E) (Q : Submodule ℝ (E ⧸ P))
      (tail : List (Submodule ℝ E))
      (hRank : Module.finrank ℝ Q = 1 ∨ Module.finrank ℝ Q = 2)
      (hInv : ∀ x ∈ P, f x ∈ P)
      (hStrict : P < Q.comap P.mkQ)
      (hTail : RealSchurInvariantFlag f ((Q.comap P.mkQ) :: tail)) :
      RealSchurInvariantFlag f (P :: (Q.comap P.mkQ) :: tail)

/-- Every finite-dimensional real endomorphism has a complete
invariant flag with one- or two-dimensional quotient increments.
This is the algebraic part of the global real-Schur decomposition;
orthonormal coordinates and the Gaussian change of variables are
separate steps. -/
theorem realLinearMap_exists_invariant_flag
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) :
    ∃ tail : List (Submodule ℝ E),
      RealSchurInvariantFlag f (⊥ :: tail) := by
  have aux : ∀ n : ℕ, ∀ P : Submodule ℝ E,
      (∀ x ∈ P, f x ∈ P) →
      Module.finrank ℝ (E ⧸ P) = n →
      ∃ tail : List (Submodule ℝ E),
        RealSchurInvariantFlag f (P :: tail) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P hInv hDim
      by_cases hzero : n = 0
      · have hsum := P.finrank_quotient_add_finrank
        have hRank : Module.finrank ℝ P = Module.finrank ℝ E := by omega
        have hTop : P = ⊤ := Submodule.eq_top_of_finrank_eq hRank
        subst P
        exact ⟨[], RealSchurInvariantFlag.done⟩
      · have hquot : 0 < Module.finrank ℝ (E ⧸ P) := by omega
        obtain ⟨Q,hRank,hStrict,hInvT⟩ :=
          realLinearMap_invariant_subspace_strict_extension f P hInv hquot
        let T : Submodule ℝ E := Q.comap P.mkQ
        have hLess : Module.finrank ℝ (E ⧸ T) < n := by
          have hRankStrict : Module.finrank ℝ P < Module.finrank ℝ T :=
            Submodule.finrank_lt_finrank_of_lt hStrict
          have hsumP := P.finrank_quotient_add_finrank
          have hsumT := T.finrank_quotient_add_finrank
          omega
        obtain ⟨tail,hTail⟩ := ih _ hLess T hInvT rfl
        refine ⟨T :: tail, ?_⟩
        change RealSchurInvariantFlag f (P :: Q.comap P.mkQ :: tail)
        exact RealSchurInvariantFlag.step P Q tail hRank hInv hStrict hTail
  apply aux _ ⊥
  · intro x hx
    have hx0 : x = 0 := by simpa using hx
    subst x
    simp
  · rfl

#print axioms realLinearMap_exists_invariant_flag
end SpectralRadiusUpperTail
