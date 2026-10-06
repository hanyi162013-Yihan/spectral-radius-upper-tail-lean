import SpectralRadiusUpperTail.RealSchurInvariantQuotient
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The quotient correspondence preserves the exact dimension of an
increment: pulling back a quotient subspace adds precisely its rank
to the rank of the original subspace. -/
theorem realSchur_finrank_comap_mkQ
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (P : Submodule ℝ E) (Q : Submodule ℝ (E ⧸ P)) :
    Module.finrank ℝ (Q.comap P.mkQ) =
      Module.finrank ℝ P + Module.finrank ℝ Q := by
  let T : Submodule ℝ E := Q.comap P.mkQ
  let g : T →ₗ[ℝ] E ⧸ P := P.mkQ.domRestrict T
  have hRange : LinearMap.range g = Q := by
    change LinearMap.range (P.mkQ.domRestrict T) = Q
    rw [LinearMap.range_domRestrict]
    exact Submodule.map_comap_eq_self (by simp)
  have hKer : LinearMap.ker g = P.comap T.subtype := by
    simp [g, LinearMap.ker_domRestrict]
  have hPLe : P ≤ T := Submodule.le_comap_mkQ P Q
  have hKerRank : Module.finrank ℝ (LinearMap.ker g) = Module.finrank ℝ P := by
    rw [hKer]
    exact (Submodule.comapSubtypeEquivOfLe hPLe).finrank_eq
  have hsum := g.finrank_range_add_finrank_ker
  rw [hRange, hKerRank] at hsum
  change Module.finrank ℝ Q + Module.finrank ℝ P =
    Module.finrank ℝ (Q.comap P.mkQ) at hsum
  omega

#print axioms realSchur_finrank_comap_mkQ
end SpectralRadiusUpperTail
