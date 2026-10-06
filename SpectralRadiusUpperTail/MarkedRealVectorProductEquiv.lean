import SpectralRadiusUpperTail.MarkedRealStereoCoverage

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Scalar/complement splitting of a marked column, as a linear equivalence. -/
def markedRealVectorProductEquiv (m : ℕ) :
    (ℝ × (Fin m → ℝ)) ≃ₗ[ℝ]
      (RealSchurMixedCoord (markedRealTwoBlockSizes m) → ℝ) where
  toFun x := markedRealVectorCons m x.1 x.2
  invFun v := (v (markedRealFirstCoordinate m), fun i => v ⟨1,i⟩)
  left_inv x := by
    apply Prod.ext
    · exact markedRealVectorCons_first m x.1 x.2
    · exact funext (markedRealVectorCons_complement m x.1 x.2)
  right_inv := markedRealVectorCons_reconstruct m
  map_add' x y := by
    apply markedRealVectorCons_ext m
    · simp only [markedRealVectorCons_first, Pi.add_apply, Prod.fst_add]
    · intro i
      simp only [markedRealVectorCons_complement, Pi.add_apply, Prod.snd_add]
  map_smul' a x := by
    apply markedRealVectorCons_ext m
    · simp only [markedRealVectorCons_first, Pi.smul_apply]
      rfl
    · intro i
      simp only [markedRealVectorCons_complement, Pi.smul_apply]
      rfl

theorem markedRealVectorProductEquiv_symm_apply (m : ℕ)
    (v : RealSchurMixedCoord (markedRealTwoBlockSizes m) → ℝ) :
    (markedRealVectorProductEquiv m).symm v =
      (v (markedRealFirstCoordinate m), fun i => v ⟨1,i⟩) := rfl

#print axioms markedRealVectorProductEquiv
#print axioms markedRealVectorProductEquiv_symm_apply
end SpectralRadiusUpperTail
