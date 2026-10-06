import SpectralRadiusUpperTail.MatrixRootExteriorCounts
import SpectralRadiusUpperTail.MatrixMoments
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

noncomputable def matrixExteriorRootCount {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) (i : Fin 3) : ℕ :=
  if i = 0 then matrixPositiveRealRootCount A r
  else if i = 1 then matrixNegativeRealRootCount A r
  else matrixNonrealExteriorRootCount A r

theorem matrixExteriorRootCount_le_dim {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) (i : Fin 3) :
    matrixExteriorRootCount A r i ≤ n := by
  classical
  have hcard : A.charpoly.roots.card = n := by
    rw [← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  fin_cases i
  · simpa [matrixExteriorRootCount, matrixPositiveRealRootCount] using
      (Multiset.countP_le_card (p := fun z : ℂ => z.im = 0 ∧ r < z.re)
        A.charpoly.roots).trans_eq hcard
  · simpa [matrixExteriorRootCount, matrixNegativeRealRootCount] using
      (Multiset.countP_le_card (p := fun z : ℂ => z.im = 0 ∧ z.re < -r)
        A.charpoly.roots).trans_eq hcard
  · simpa [matrixExteriorRootCount, matrixNonrealExteriorRootCount] using
      (Multiset.countP_le_card (p := fun z : ℂ => z.im ≠ 0 ∧ r < ‖z‖)
        A.charpoly.roots).trans_eq hcard

/-- The three actual root counts for the normalized real matrix. -/
noncomputable def realGaussianExteriorCount (n : ℕ) (r : ℝ)
    (i : Fin 3) (x : (Fin n × Fin n) → ℝ) : ℝ :=
  (matrixExteriorRootCount
    (((1/Real.sqrt (n : ℝ)) • entryMatrix x).map Complex.ofRealHom)
    r i : ℕ)

theorem realGaussianExteriorCount_bounds (n : ℕ) (r : ℝ)
    (i : Fin 3) (x : (Fin n × Fin n) → ℝ) :
    0 ≤ realGaussianExteriorCount n r i x ∧
    (0 < realGaussianExteriorCount n r i x →
      1 ≤ realGaussianExteriorCount n r i x) ∧
    realGaussianExteriorCount n r i x ≤ (n : ℝ) := by
  let k := matrixExteriorRootCount
    (((1/Real.sqrt (n : ℝ)) • entryMatrix x).map Complex.ofRealHom) r i
  have hk : k ≤ n := matrixExteriorRootCount_le_dim _ r i
  change 0 ≤ (k : ℝ) ∧
    (0 < (k : ℝ) → 1 ≤ (k : ℝ)) ∧ (k : ℝ) ≤ (n : ℝ)
  constructor
  · positivity
  constructor
  · intro h
    have hkpos : 0 < k := by exact_mod_cast h
    exact_mod_cast (show 1 ≤ k by omega)
  · exact_mod_cast hk

/-- The spectral-radius event is exactly the union of the positive-real,
negative-real, and nonreal exterior root-count events. -/
theorem realGaussianExteriorCount_cover (n : ℕ) (hn : 0 < n)
    (r : ℝ) (x : (Fin n × Fin n) → ℝ) :
    r < realMatrixRadius ((1/Real.sqrt (n : ℝ)) • entryMatrix x) ↔
      0 < realGaussianExteriorCount n r 0 x ∨
      0 < realGaussianExteriorCount n r 1 x ∨
      0 < realGaussianExteriorCount n r 2 x := by
  have h := matrix_radius_exterior_count_cover hn
    (((1/Real.sqrt (n : ℝ)) • entryMatrix x).map Complex.ofRealHom) r
  simpa [realMatrixRadius, realGaussianExteriorCount,
    matrixExteriorRootCount] using h

#print axioms matrixExteriorRootCount_le_dim
#print axioms realGaussianExteriorCount_bounds
#print axioms realGaussianExteriorCount_cover
end SpectralRadiusUpperTail
