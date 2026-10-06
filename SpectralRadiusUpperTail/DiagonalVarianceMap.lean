import SpectralRadiusUpperTail.MatrixCoordinateSquare

namespace SpectralRadiusUpperTail
open Matrix
variable {𝕂 : Type*} [RCLike 𝕂] {N : ℕ}

/-- A real scalar placed on the two diagonal coordinates selected by a
matrix entry. Its codomain carries the finite-function norm. -/
noncomputable def dilationVarianceCoordinateL (i j : Fin N) :
    ℝ →L[ℝ] ((Fin N ⊕ Fin N) → (Fin N ⊕ Fin N) → 𝕂) :=
  ContinuousLinearMap.pi fun p => ContinuousLinearMap.pi fun q =>
    if p=q then
      match p with
      | Sum.inl k => if k=i then RCLike.ofRealCLM else 0
      | Sum.inr k => if k=j then RCLike.ofRealCLM else 0
    else 0

lemma dilationVarianceCoordinateL_apply (i j : Fin N) (r : ℝ)
    (p q : Fin N ⊕ Fin N) :
    dilationVarianceCoordinateL (𝕂 := 𝕂) i j r p q =
      if p=q then
        match p with
        | Sum.inl k => if k=i then (r : 𝕂) else 0
        | Sum.inr k => if k=j then (r : 𝕂) else 0
      else 0 := by
  unfold dilationVarianceCoordinateL
  simp only [ContinuousLinearMap.pi_apply]
  by_cases h : p=q
  · simp only [if_pos h]
    cases p <;> dsimp only <;> split_ifs <;> rfl
  · simp [h]

lemma dilationVarianceCoordinateL_blocks (i j : Fin N) (r : ℝ) :
    dilationVarianceCoordinateL (𝕂 := 𝕂) i j r =
      Matrix.fromBlocks (Matrix.single i i (r : 𝕂)) 0 0 (Matrix.single j j (r : 𝕂)) := by
  ext p q
  rw [dilationVarianceCoordinateL_apply]
  cases p with
  | inl p => cases q with
    | inl q =>
      by_cases hp : p=i
      · subst p
        simp [Matrix.fromBlocks, Matrix.single]
      · simp [Matrix.fromBlocks, Matrix.single, hp, Ne.symm hp]
    | inr q => simp [Matrix.fromBlocks]
  | inr p => cases q with
    | inl q => simp [Matrix.fromBlocks]
    | inr q =>
      by_cases hp : p=j
      · subst p
        simp [Matrix.fromBlocks, Matrix.single]
      · simp [Matrix.fromBlocks, Matrix.single, hp, Ne.symm hp]

/-- The normalized actual dilation square is a continuous real linear
image of the scalar squared norm, so its conditional expectation can be
transported without changing the normed codomain instance. -/
lemma scaled_matrixCoordinate_dilation_square (i j : Fin N) (z : 𝕂) (c : ℝ) :
    hermitianDilation (c • matrixCoordinateL i j z) * hermitianDilation (c • matrixCoordinateL i j z) =
      (c^2 • dilationVarianceCoordinateL (𝕂 := 𝕂) i j) (‖z‖^2) := by
  rw [← map_smul, matrixCoordinate_dilation_square, ← dilationVarianceCoordinateL_blocks]
  have he : ‖c • z‖^2 = c^2*‖z‖^2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [he, ← smul_eq_mul, map_smul]
  rfl

#print axioms scaled_matrixCoordinate_dilation_square
end SpectralRadiusUpperTail
