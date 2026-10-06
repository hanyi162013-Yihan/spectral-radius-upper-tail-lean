import SpectralRadiusUpperTail.RealGaussianRootCountInterface
import SpectralRadiusUpperTail.MatrixCharpolyScalarRoots
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The three exterior regions tested by the real Gaussian radius
argument, on a complex characteristic root. -/
def realGaussianExteriorPredicate (r : ℝ) (i : Fin 3)
    (z : ℂ) : Prop :=
  if i = 0 then z.im = 0 ∧ r < z.re
  else if i = 1 then z.im = 0 ∧ z.re < -r
  else z.im ≠ 0 ∧ r < ‖z‖

theorem matrixExteriorRootCount_eq_countP {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) (i : Fin 3) :
    matrixExteriorRootCount A r i =
      (by
        classical
        exact Multiset.countP
          (realGaussianExteriorPredicate r i) A.charpoly.roots) := by
  classical
  fin_cases i <;>
    simp [matrixExteriorRootCount, realGaussianExteriorPredicate,
      matrixPositiveRealRootCount, matrixNegativeRealRootCount,
      matrixNonrealExteriorRootCount]
  all_goals congr 1

/-- Remove the `n⁻¹ᐟ²` matrix normalization from an actual root count by
putting it into the predicate on the unscaled roots. -/
theorem realGaussianExteriorCount_eq_unscaled_countP
    (n : ℕ) (hn : 0 < n) (r : ℝ) (i : Fin 3)
    (x : (Fin n × Fin n) → ℝ) :
    realGaussianExteriorCount n r i x =
      (((by
        classical
        exact Multiset.countP
          (fun z : ℂ => realGaussianExteriorPredicate r i
            ((((1/Real.sqrt (n : ℝ)) : ℝ) : ℂ) * z))
          ((Matrix.of x.curry).charpoly.aroots ℂ)) : ℕ) : ℝ) := by
  classical
  let c : ℂ := (((1/Real.sqrt (n : ℝ)) : ℝ) : ℂ)
  let A : Matrix (Fin n) (Fin n) ℂ :=
    (Matrix.of x.curry).map Complex.ofRealHom
  have hsqrt : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.mpr hn)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact Complex.ofReal_ne_zero.mpr (one_div_ne_zero hsqrt.ne')
  have hmatrix : (((1/Real.sqrt (n : ℝ)) • Matrix.of x.curry).map
      Complex.ofRealHom) = c • A := by
    ext a b
    simp [A, c, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  unfold realGaussianExteriorCount
  have hentry : entryMatrix x = Matrix.of x.curry := rfl
  rw [matrixExteriorRootCount_eq_countP, hentry, hmatrix,
    matrix_charpoly_smul_roots A c hc]
  rw [Matrix.charpoly_map]
  congr 1
  rw [Multiset.countP_map]
  rw [Multiset.countP_eq_card_filter]
  rfl

#print axioms realGaussianExteriorCount_eq_unscaled_countP
end SpectralRadiusUpperTail
