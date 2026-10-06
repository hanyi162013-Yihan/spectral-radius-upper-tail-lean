import SpectralRadiusUpperTail.RealRankOneReflection
import SpectralRadiusUpperTail.MarkedRealVectorCons
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

noncomputable def markedRealStereoDenom (m : ℕ) (u : Fin m → ℝ) : ℝ :=
  1 + u ⬝ᵥ u

theorem markedRealStereoDenom_pos (m : ℕ) (u : Fin m → ℝ) :
    0 < markedRealStereoDenom m u := by
  have h : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg (fun i _ => mul_self_nonneg (u i))
  unfold markedRealStereoDenom
  linarith

def markedRealFirstSign (m : ℕ) : RealSchurMixedCoord (markedRealTwoBlockSizes m) → ℝ :=
  markedRealVectorCons m (-1) (fun _ => 1)

theorem markedRealFirstSign_sq (m : ℕ)
    (i : RealSchurMixedCoord (markedRealTwoBlockSizes m)) :
    markedRealFirstSign m i * markedRealFirstSign m i = 1 := by
  unfold markedRealFirstSign markedRealVectorCons
  split_ifs <;> norm_num

/-- An explicit smooth orthogonal completion of stereographic coordinates.
It is defined on all parameters, and its first column lies in the positive
hemisphere when `u ⬝ᵥ u < 1`. -/
noncomputable def markedRealStereoFrame (m : ℕ) (u : Fin m → ℝ) :
    Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ :=
  realRankOneReflection (markedRealVectorCons m 1 u) *
    Matrix.diagonal (markedRealFirstSign m)

theorem markedRealStereoFrame_apply (m : ℕ) (u : Fin m → ℝ)
    (i j : RealSchurMixedCoord (markedRealTwoBlockSizes m)) :
    markedRealStereoFrame m u i j =
      ((1 : Matrix _ _ ℝ) i j -
        (2/markedRealStereoDenom m u)*(markedRealVectorCons m 1 u i *
          markedRealVectorCons m 1 u j))*markedRealFirstSign m j := by
  simp only [markedRealStereoFrame, Matrix.mul_diagonal,
    realRankOneReflection, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, markedRealVectorCons_dot,
    one_mul, markedRealStereoDenom]

theorem markedRealStereoFrame_orthogonal (m : ℕ) (u : Fin m → ℝ) :
    (markedRealStereoFrame m u)ᵀ * markedRealStereoFrame m u = 1 := by
  let H := realRankOneReflection (markedRealVectorCons m 1 u)
  let D := Matrix.diagonal (markedRealFirstSign m)
  have hH : Hᵀ*H=1 := realRankOneReflection_orthogonal _ (by
    simpa only [markedRealVectorCons_dot, one_mul, markedRealStereoDenom] using
      (markedRealStereoDenom_pos m u).ne')
  change (H*D)ᵀ*(H*D)=1
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Hᵀ H,
    hH, Matrix.one_mul]
  change (Matrix.diagonal (markedRealFirstSign m))ᵀ * Matrix.diagonal (markedRealFirstSign m) = 1
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    markedRealFirstSign_sq, Matrix.diagonal_one]

theorem markedRealStereoFrame_first_first (m : ℕ) (u : Fin m → ℝ) :
    markedRealStereoFrame m u (markedRealFirstCoordinate m) (markedRealFirstCoordinate m) =
      (1-u ⬝ᵥ u)/markedRealStereoDenom m u := by
  rw [markedRealStereoFrame_apply]
  simp only [Matrix.one_apply_eq, markedRealVectorCons_first,
    markedRealFirstSign, one_mul]
  have hd : 1+u ⬝ᵥ u ≠ 0 := (markedRealStereoDenom_pos m u).ne'
  unfold markedRealStereoDenom
  field_simp [hd]
  <;> ring

theorem markedRealStereoFrame_complement_first (m : ℕ) (u : Fin m → ℝ) (i : Fin m) :
    markedRealStereoFrame m u ⟨1,i⟩ (markedRealFirstCoordinate m) =
      2*u i/markedRealStereoDenom m u := by
  rw [markedRealStereoFrame_apply]
  simp only [markedRealVectorCons_complement, markedRealVectorCons_first,
    markedRealFirstSign, mul_one]
  have hne : (⟨1,i⟩ : RealSchurMixedCoord (markedRealTwoBlockSizes m)) ≠ markedRealFirstCoordinate m := by
    intro h
    have := congrArg Sigma.fst h
    norm_num [markedRealFirstCoordinate] at this
  rw [Matrix.one_apply_ne hne]
  ring

theorem markedRealStereoFrame_first_complement (m : ℕ) (u : Fin m → ℝ) (i : Fin m) :
    markedRealStereoFrame m u (markedRealFirstCoordinate m) ⟨1,i⟩ =
      -(2*u i/markedRealStereoDenom m u) := by
  rw [markedRealStereoFrame_apply]
  simp only [markedRealVectorCons_complement, markedRealVectorCons_first,
    markedRealFirstSign, one_mul, mul_one]
  have hne : markedRealFirstCoordinate m ≠ (⟨1,i⟩ : RealSchurMixedCoord (markedRealTwoBlockSizes m)) := by
    intro h
    have := congrArg Sigma.fst h
    norm_num [markedRealFirstCoordinate] at this
  rw [Matrix.one_apply_ne hne]
  ring

theorem markedRealStereoFrame_complement_complement
    (m : ℕ) (u : Fin m → ℝ) (i j : Fin m) :
    markedRealStereoFrame m u ⟨1,i⟩ ⟨1,j⟩ =
      (1 : Matrix (Fin m) (Fin m) ℝ) i j -
        (2/markedRealStereoDenom m u)*(u i*u j) := by
  rw [markedRealStereoFrame_apply]
  simp only [markedRealVectorCons_complement, markedRealFirstSign, mul_one]
  congr 1
  simp [Matrix.one_apply]

#print axioms markedRealStereoDenom_pos
#print axioms markedRealStereoFrame_orthogonal
#print axioms markedRealStereoFrame_first_first
#print axioms markedRealStereoFrame_complement_first
#print axioms markedRealStereoFrame_first_complement
#print axioms markedRealStereoFrame_complement_complement
end SpectralRadiusUpperTail
