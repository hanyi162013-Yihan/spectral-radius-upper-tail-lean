import SpectralRadiusUpperTail.RealSchurMixedFullChartJacobian
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Vanishing of the projected lower block is exactly block-upper
triangularity on the global scalar-coordinate matrix. -/
theorem realSchurMixed_blockTriangular_iff_lower_zero
    {m : ℕ} (s : Fin m → ℕ)
    (A : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    A.BlockTriangular (fun z : RealSchurMixedCoord s => z.1) ↔
      realSchurMixedLowerProjection s A = 0 := by
  constructor
  · intro h
    funext p
    exact h (i := ⟨p.1.1.1,p.2.1⟩) (j := ⟨p.1.1.2,p.2.2⟩) p.1.2
  · intro h u v hvu
    let p : RealSchurMixedOrbitIndex s :=
      ⟨⟨(u.1,v.1),hvu⟩,(u.2,v.2)⟩
    exact congrFun h p

theorem realSchurMixedLowerProjection_mul_zero
    {m : ℕ} (s : Fin m → ℕ)
    (A B : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hA : realSchurMixedLowerProjection s A = 0)
    (hB : realSchurMixedLowerProjection s B = 0) :
    realSchurMixedLowerProjection s (A*B) = 0 := by
  apply (realSchurMixed_blockTriangular_iff_lower_zero s (A*B)).mp
  exact ((realSchurMixed_blockTriangular_iff_lower_zero s A).mpr hA).mul
    ((realSchurMixed_blockTriangular_iff_lower_zero s B).mpr hB)

theorem realSchurMixedLowerProjection_upper_commutator_zero
    {m : ℕ} (s : Fin m → ℕ)
    (A B : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hA : realSchurMixedLowerProjection s A = 0)
    (hB : realSchurMixedLowerProjection s B = 0) :
    realSchurMixedLowerProjection s (A*B-B*A) = 0 := by
  rw [map_sub, realSchurMixedLowerProjection_mul_zero s A B hA hB,
    realSchurMixedLowerProjection_mul_zero s B A hB hA, sub_self]

#print axioms realSchurMixed_blockTriangular_iff_lower_zero
#print axioms realSchurMixedLowerProjection_mul_zero
end SpectralRadiusUpperTail
