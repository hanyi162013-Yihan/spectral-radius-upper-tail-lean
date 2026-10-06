import SpectralRadiusUpperTail.MarkedRealUpperEigenvector

namespace SpectralRadiusUpperTail
open scoped Matrix

theorem markedReal_firstColumn_eigenvector_implies_upper (m : ℕ)
    (S : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (z : ℝ)
    (hS : S *ᵥ Pi.single (markedRealFirstCoordinate m) 1 =
      z • Pi.single (markedRealFirstCoordinate m) 1) :
    realSchurMixedLowerProjection (markedRealTwoBlockSizes m) S = 0 ∧
      markedRealScalar m S = z := by
  constructor
  · funext q
    obtain ⟨i, rfl⟩ := (markedRealOrbitEquiv m).surjective q
    have hi := congrFun hS (⟨1,i⟩ : RealSchurMixedCoord (markedRealTwoBlockSizes m))
    change S ⟨1,i⟩ (markedRealFirstCoordinate m) = 0
    simpa [Matrix.mulVec_single_one, markedRealFirstCoordinate] using hi
  · have hi := congrFun hS (markedRealFirstCoordinate m)
    simpa [Matrix.mulVec_single_one, markedRealScalar] using hi

/-- An orthogonal frame whose first column is an eigenvector supplies
the required block-upper matrix, with the prescribed scalar root. -/
theorem markedReal_orthogonal_eigenColumn_upper (m : ℕ)
    (A Q : Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
      (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ)
    (hQ : Qᵀ*Q=1) (z : ℝ)
    (hAz : A *ᵥ (fun i => Q i (markedRealFirstCoordinate m)) =
      z • (fun i => Q i (markedRealFirstCoordinate m))) :
    ∃ S : realSchurMixedUpperSubmodule (markedRealTwoBlockSizes m),
      markedRealScalar m S.val = z ∧ A = Q*S.val*Qᵀ := by
  let e : RealSchurMixedCoord (markedRealTwoBlockSizes m) → ℝ :=
    Pi.single (markedRealFirstCoordinate m) 1
  have hcol : Q *ᵥ e = fun i => Q i (markedRealFirstCoordinate m) :=
    Matrix.mulVec_single_one _ _
  have hT : (Qᵀ*A*Q) *ᵥ e = z • e := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol, hAz,
      Matrix.mulVec_smul, ← hcol, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]
  obtain ⟨hu,hz⟩ := markedReal_firstColumn_eigenvector_implies_upper m (Qᵀ*A*Q) z hT
  have hQQ : Q*Qᵀ=1 := mul_eq_one_comm.mp hQ
  refine ⟨⟨Qᵀ*A*Q, hu⟩, hz, ?_⟩
  change A = Q*(Qᵀ*A*Q)*Qᵀ
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Q Qᵀ, hQQ,
    Matrix.one_mul, Matrix.mul_one]

#print axioms markedReal_firstColumn_eigenvector_implies_upper
#print axioms markedReal_orthogonal_eigenColumn_upper
end SpectralRadiusUpperTail
