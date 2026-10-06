import SpectralRadiusUpperTail.RealSchurMixedSkewCoordinates
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- For a block-upper matrix, the lower part of a commutator depends
only on the lower entries of its first argument. This is the algebraic
moving-frame identity needed away from the chart center. -/
theorem realSchurMixedLowerProjection_commutator
    {m : ℕ} (s : Fin m → ℕ)
    (S K : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hS : realSchurMixedLowerProjection s S = 0) :
    realSchurMixedLowerProjection s (K*S-S*K) =
      -(realSchurMixedOrbitMatrix s S).mulVec
        (realSchurMixedLowerProjection s K) := by
  let ω := realSchurMixedLowerProjection s K
  have hres : realSchurMixedLowerProjection s
      (K + realSchurMixedSkewEmbed s ω) = 0 := by
    rw [map_add, realSchurMixedLowerProjection_skewEmbed]
    exact add_neg_cancel ω
  have hz := realSchurMixedLowerProjection_upper_commutator_zero s
    (K + realSchurMixedSkewEmbed s ω) S hres hS
  funext p
  have hp := congrFun hz p
  have hk := realSchurMixedSkewEmbed_lower_action s S ω p
  change ((K + realSchurMixedSkewEmbed s ω)*S -
      S*(K + realSchurMixedSkewEmbed s ω))
      ⟨p.1.1.1,p.2.1⟩ ⟨p.1.1.2,p.2.2⟩ = 0 at hp
  change (K*S-S*K) ⟨p.1.1.1,p.2.1⟩
    ⟨p.1.1.2,p.2.2⟩ = -_ 
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_apply,
    Matrix.add_apply] at hp
  simp only [Matrix.sub_apply] at hk ⊢
  linear_combination hp - hk

#print axioms realSchurMixedLowerProjection_commutator
end SpectralRadiusUpperTail
