import SpectralRadiusUpperTail.RealMatrixColumnDifferential
import SpectralRadiusUpperTail.MarkedRealStereoRadialDifferential
import SpectralRadiusUpperTail.MarkedRealVectorProductEquiv

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators Matrix.Norms.Operator

noncomputable def markedRealStereoColumn (m : ℕ) (u : Fin m → ℝ) :
    RealSchurMixedCoord (markedRealTwoBlockSizes m) → ℝ :=
  realMatrixColumnCLM _ (markedRealFirstCoordinate m) (markedRealStereoFrame m u)

theorem markedRealStereoColumn_contDiff (m : ℕ) :
    ContDiff ℝ ⊤ (markedRealStereoColumn m) :=
  (realMatrixColumnCLM _ (markedRealFirstCoordinate m)).contDiff.comp
    (markedRealStereoFrame_contDiff m)

theorem markedRealStereoColumn_fderiv (m : ℕ) (u h : Fin m → ℝ) :
    fderiv ℝ (markedRealStereoColumn m) u h =
      fun i => (fderiv ℝ (markedRealStereoFrame m) u h) i
        (markedRealFirstCoordinate m) :=
  realMatrixColumn_fderiv (markedRealStereoFrame m) u h
    (markedRealStereoFrame_differentiable m u) (markedRealFirstCoordinate m)

theorem markedRealStereoColumn_unit (m : ℕ) (u : Fin m → ℝ) :
    ∑ i, (markedRealStereoColumn m u i)^2 = 1 := by
  change (∑ i, (markedRealStereoFrame m u i (markedRealFirstCoordinate m))^2) = 1
  have hh := congrArg (fun A => A (markedRealFirstCoordinate m) (markedRealFirstCoordinate m))
    (markedRealStereoFrame_orthogonal m u)
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq,
    ← pow_two] using hh

theorem markedRealStereoColumn_rotated (m : ℕ) (u : Fin m → ℝ) :
    (markedRealStereoFrame m u)ᵀ *ᵥ markedRealStereoColumn m u =
      markedRealVectorCons m 1 (fun _ => 0) := by
  have hh := congrArg (fun A => fun i => A i (markedRealFirstCoordinate m))
    (markedRealStereoFrame_orthogonal m u)
  apply markedRealVectorCons_ext m
  · have hi := congrFun hh (markedRealFirstCoordinate m)
    rw [markedRealVectorCons_first]
    change ((markedRealStereoFrame m u)ᵀ * markedRealStereoFrame m u)
      (markedRealFirstCoordinate m) (markedRealFirstCoordinate m) = 1
    simpa only [markedRealVectorCons_first, Matrix.one_apply_eq] using hi
  · intro i
    have hi := congrFun hh (⟨1,i⟩ : RealSchurMixedCoord (markedRealTwoBlockSizes m))
    rw [markedRealVectorCons_complement]
    change ((markedRealStereoFrame m u)ᵀ * markedRealStereoFrame m u)
      ⟨1,i⟩ (markedRealFirstCoordinate m) = 0
    simpa [markedRealVectorCons_complement, Matrix.one_apply, markedRealFirstCoordinate] using hi

theorem markedRealStereoColumn_fderiv_rotated (m : ℕ) (u h : Fin m → ℝ) :
    (markedRealStereoFrame m u)ᵀ *ᵥ fderiv ℝ (markedRealStereoColumn m) u h =
      markedRealVectorCons m 0 ((2/markedRealStereoDenom m u) • h) := by
  rw [markedRealStereoColumn_fderiv]
  apply markedRealVectorCons_ext m
  · rw [markedRealVectorCons_first]
    exact markedRealStereoFrame_moving_first m u h
  · intro i
    rw [markedRealVectorCons_complement]
    exact markedRealStereoFrame_moving_column m u h i

#print axioms markedRealStereoColumn_contDiff
#print axioms markedRealStereoColumn_fderiv
#print axioms markedRealStereoColumn_unit
#print axioms markedRealStereoColumn_rotated
#print axioms markedRealStereoColumn_fderiv_rotated
end SpectralRadiusUpperTail
