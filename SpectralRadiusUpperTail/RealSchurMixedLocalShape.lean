import SpectralRadiusUpperTail.RealSchurMixedFullChart
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- Every parameter of the local chart is an actual orthogonal conjugate
of a block-upper-triangular real matrix. The diagonal 2×2 blocks may vary
freely inside this chart; canonicalizing them is a later change of variables. -/
theorem realSchurMixedExpCoordinates_orthogonal_block_upper
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin (s a), ∀ y : Fin (s b), T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (x : RealSchurMixedTangent s) :
    ∃ Q S : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ,
      Qᵀ*Q = 1 ∧ realSchurMixedLowerProjection s S = 0 ∧
        realSchurMixedExpCoordinates s T x = Q*S*Qᵀ := by
  let Q := realSchurMixedAngularFrame s x.1
  let S := T+x.2.val
  have hprojT : realSchurMixedLowerProjection s T = 0 := by
    funext p
    exact hT p.1.1.1 p.1.1.2 p.1.2 p.2.1 p.2.2
  refine ⟨Q,S,realSchurMixedAngularFrame_orthogonal s x.1,?_ ,?_⟩
  · change realSchurMixedLowerProjection s (T+x.2.val) = 0
    rw [map_add, hprojT, zero_add]
    exact x.2.property
  · exact realSchurMixedExpCoordinates_eq_conjugation s T x

#print axioms realSchurMixedExpCoordinates_orthogonal_block_upper
end SpectralRadiusUpperTail
