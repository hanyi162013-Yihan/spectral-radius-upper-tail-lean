import SpectralRadiusUpperTail.RealSchurLowerDistanceOrder
import SpectralRadiusUpperTail.RealSchurBridgeBasis
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- One skew angular direction coupling two real conjugate-pair blocks.
The lower-block sign makes the diagonal coefficient the positive Sylvester
operator used in the pair–pair gap factor. -/
def realSchurPairOrbitGenerator {m : ℕ}
    (q : RealSchurLowerIndex m) (a : Fin 4) :
    Matrix (Fin m) (Fin m) (Matrix (Fin 2) (Fin 2) ℝ) :=
  let X := realSchurBridgeBasis a
  Matrix.single q.1.1 q.1.2 (-X) + Matrix.single q.1.2 q.1.1 Xᵀ

/-- Angular-to-lower-block derivative for an all-pair real Schur chart. -/
def realSchurAllPairOrbitMatrix {m : ℕ}
    (T : Matrix (Fin m) (Fin m) (Matrix (Fin 2) (Fin 2) ℝ)) :
    Matrix (RealSchurLowerIndex m × Fin 4)
      (RealSchurLowerIndex m × Fin 4) ℝ :=
  fun p q =>
    let K := realSchurPairOrbitGenerator q.1 q.2
    (realSchurBridgeVector ((K*T-T*K) p.1.1.1 p.1.1.2)) p.2

/-- The all-pair angular derivative is triangular in lower-block distance
and has no couplings between distinct blocks at the same distance. -/
theorem realSchurAllPairOrbitMatrix_blockTriangular {m : ℕ}
    (T : Matrix (Fin m) (Fin m) (Matrix (Fin 2) (Fin 2) ℝ))
    (hT : ∀ a b : Fin m, b < a → T a b = 0) :
    (realSchurAllPairOrbitMatrix T).BlockTriangular
      (fun p => realSchurLowerKey p.1) := by
  intro p q hqp
  let X := realSchurBridgeBasis q.2
  have hcases := realSchurLower_lt_cases q.1 p.1 hqp
  have hz :
      ((realSchurPairOrbitGenerator q.1 q.2)*T -
        T*(realSchurPairOrbitGenerator q.1 q.2))
          p.1.1.1 p.1.1.2 = 0 := by
    rcases hcases with hfar | ⟨hdist, hneq⟩
    · have hfar' : q.1.1.1.val-q.1.1.2.val <
          p.1.1.1.val-p.1.1.2.val := hfar
      simpa only [realSchurPairOrbitGenerator, X] using
        (realSchur_block_orbit_distance_support T hT
          q.1.1.1 q.1.1.2 p.1.1.1 p.1.1.2
          q.1.2 p.1.2 hfar' (-X) Xᵀ)
    · have hdist' : q.1.1.1.val-q.1.1.2.val =
          p.1.1.1.val-p.1.1.2.val := congrArg Fin.val hdist
      have hneq' : (p.1.1.1, p.1.1.2) ≠ (q.1.1.1, q.1.1.2) := by
        intro heq
        exact hneq (Subtype.ext heq.symm)
      simpa only [realSchurPairOrbitGenerator, X] using
        (realSchur_block_orbit_same_distance_offdiagonal T hT
          q.1.1.1 q.1.1.2 p.1.1.1 p.1.1.2
          q.1.2 p.1.2 hdist' hneq' (-X) Xᵀ)
  change (realSchurBridgeVector
    (((realSchurPairOrbitGenerator q.1 q.2)*T -
      T*(realSchurPairOrbitGenerator q.1 q.2))
        p.1.1.1 p.1.1.2)) p.2 = 0
  rw [hz]
  rcases p with ⟨p, a⟩
  fin_cases a <;> rfl

/-- The diagonal 4×4 fiber of the all-pair orbit derivative is exactly
the pair–pair Sylvester matrix. -/
theorem realSchurAllPairOrbitMatrix_diagonal {m : ℕ}
    (T : Matrix (Fin m) (Fin m) (Matrix (Fin 2) (Fin 2) ℝ))
    (p : RealSchurLowerIndex m)
    (x b c u d e : ℝ)
    (hii : T p.1.1 p.1.1 = realSchurBlock x b c)
    (hjj : T p.1.2 p.1.2 = realSchurBlock u d e)
    (a s : Fin 4) :
    realSchurAllPairOrbitMatrix T (p,a) (p,s) =
      realSchurPairPairSylvester x b c u d e a s := by
  let X := realSchurBridgeBasis s
  have hcomm := realSchur_block_orbit_diagonal_coefficient T
    p.1.1 p.1.2 (ne_of_gt p.2) (-X) Xᵀ
  change ((realSchurPairOrbitGenerator p s)*T -
    T*(realSchurPairOrbitGenerator p s)) p.1.1 p.1.2 =
      (-X)*T p.1.2 p.1.2 - T p.1.1 p.1.1*(-X) at hcomm
  change (realSchurBridgeVector
    (((realSchurPairOrbitGenerator p s)*T -
      T*(realSchurPairOrbitGenerator p s)) p.1.1 p.1.2)) a = _
  rw [hcomm, hii, hjj]
  have hflip : (-X)*realSchurBlock u d e -
      realSchurBlock x b c*(-X) =
      realSchurBlock x b c*X - X*realSchurBlock u d e := by
    simp only [neg_mul, mul_neg]
    abel
  rw [hflip, realSchur_pair_pair_sylvester_action]
  exact realSchurBridgeBasis_sylvester_column
    (realSchurPairPairSylvester x b c u d e) s a

#print axioms realSchurAllPairOrbitMatrix_blockTriangular
#print axioms realSchurAllPairOrbitMatrix_diagonal
end SpectralRadiusUpperTail
