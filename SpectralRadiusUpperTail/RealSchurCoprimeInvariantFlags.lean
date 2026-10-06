import SpectralRadiusUpperTail.RealSchurCoprimeIntertwiner
import SpectralRadiusUpperTail.RealSchurInvariantQuotient
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- An intertwiner sends an invariant first block into another one if
the source first-block and target quotient spectra are disjoint. -/
theorem invariantSubmodule_map_le_of_coprime_charpoly
    {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]
    (f : E →ₗ[ℝ] E) (g : F →ₗ[ℝ] F)
    (P : Submodule ℝ E) (Q : Submodule ℝ F)
    (hP : ∀ x : E, x ∈ P → f x ∈ P)
    (hQ : ∀ x : F, x ∈ Q → g x ∈ Q)
    (L : E →ₗ[ℝ] F) (hinter : ∀ x : E, L (f x) = g (L x))
    (hcop : IsCoprime (f.restrict hP).charpoly
      (realLinearMapInvariantQuotient g Q hQ).charpoly) :
    ∀ x ∈ P, L x ∈ Q := by
  let M : P →ₗ[ℝ] F ⧸ Q := Q.mkQ.comp (L.comp P.subtype)
  have hM : ∀ x : P,
      M ((f.restrict hP) x) =
        (realLinearMapInvariantQuotient g Q hQ) (M x) := by
    intro x
    change Q.mkQ (L (f (x : E))) =
      (realLinearMapInvariantQuotient g Q hQ) (Q.mkQ (L x))
    rw [hinter, realLinearMapInvariantQuotient_mkQ]
  have hzero := linearMap_eq_zero_of_coprime_charpoly_intertwining
    (f.restrict hP) (realLinearMapInvariantQuotient g Q hQ)
    M hcop hM
  intro x hx
  have hz : Q.mkQ (L x) = 0 := by
    have hm := LinearMap.congr_fun hzero (⟨x,hx⟩ : P)
    change Q.mkQ (L x) = 0 at hm
    exact hm
  exact (Submodule.Quotient.mk_eq_zero Q).mp
    (by simpa only [Submodule.mkQ_apply] using hz)

/-- Two invariant flags with opposite cross-spectral separation are
equal. This is the algebraic core of ordered Schur-flag uniqueness. -/
theorem invariantSubmodules_eq_of_cross_coprime_charpoly
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E]
    (f : E →ₗ[ℝ] E) (P Q : Submodule ℝ E)
    (hP : ∀ x : E, x ∈ P → f x ∈ P)
    (hQ : ∀ x : E, x ∈ Q → f x ∈ Q)
    (hPQ : IsCoprime (f.restrict hP).charpoly
      (realLinearMapInvariantQuotient f Q hQ).charpoly)
    (hQP : IsCoprime (f.restrict hQ).charpoly
      (realLinearMapInvariantQuotient f P hP).charpoly) :
    P = Q := by
  apply le_antisymm
  · exact invariantSubmodule_map_le_of_coprime_charpoly
      f f P Q hP hQ (LinearMap.id) (by intro x; rfl) hPQ
  · exact invariantSubmodule_map_le_of_coprime_charpoly
      f f Q P hQ hP (LinearMap.id) (by intro x; rfl) hQP

#print axioms invariantSubmodule_map_le_of_coprime_charpoly
#print axioms invariantSubmodules_eq_of_cross_coprime_charpoly
end SpectralRadiusUpperTail
