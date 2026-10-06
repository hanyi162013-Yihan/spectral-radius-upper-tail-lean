import SpectralRadiusUpperTail.SchurOrbitTriangularDeterminant
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The coordinates strictly below the diagonal of an `n × n` matrix. -/
abbrev RealSchurLowerIndex (n : ℕ) :=
  {p : Fin n × Fin n // p.2 < p.1}

/-- The lower-entry projection of the commutator with one elementary skew
direction. Its matrix is the angular-to-lower-entry derivative in the
all-scalar Schur chart. -/
def realSchurScalarOrbitMatrix {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (RealSchurLowerIndex n) (RealSchurLowerIndex n) ℝ :=
  fun p q =>
    let K : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.single q.1.1 q.1.2 1 - Matrix.single q.1.2 q.1.1 1
    (K*T-T*K) p.1.1 p.1.2

/-- Distance below the diagonal is a finite block index for the angular
derivative. -/
def realSchurLowerDistance {n : ℕ} (p : RealSchurLowerIndex n) : Fin n :=
  ⟨p.1.1.val-p.1.2.val,
    lt_of_le_of_lt (Nat.sub_le _ _) p.1.1.isLt⟩

/-- The complete scalar-block angular determinant is the Vandermonde-type
product of diagonal gaps. This is a determinant of a concrete finite matrix,
not yet a change-of-variables theorem for the orthogonal Schur atlas. -/
theorem realSchur_scalar_orbit_det
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ a b : Fin n, b < a → T a b = 0) :
    (realSchurScalarOrbitMatrix T).det =
      ∏ p : RealSchurLowerIndex n, (T p.1.2 p.1.2-T p.1.1 p.1.1) := by
  classical
  have htri : (realSchurScalarOrbitMatrix T).BlockTriangular realSchurLowerDistance := by
    intro p q hpq
    exact realSchur_scalar_orbit_distance_support T hT
      q.1.1 q.1.2 p.1.1 p.1.2 q.2 p.2 hpq 1
  have hfiber : ∀ p q : RealSchurLowerIndex n,
      realSchurLowerDistance p = realSchurLowerDistance q →
      p ≠ q → (realSchurScalarOrbitMatrix T) p q = 0 := by
    intro p q hdist hne
    apply realSchur_scalar_orbit_same_distance_offdiagonal T hT
      q.1.1 q.1.2 p.1.1 p.1.2 q.2 p.2
    · exact congrArg Fin.val hdist.symm
    · exact fun h => hne (Subtype.ext h)
  rw [determinant_of_block_triangular_fiber_diagonal
    (realSchurScalarOrbitMatrix T) realSchurLowerDistance htri hfiber]
  apply Finset.prod_congr rfl
  intro p _
  simpa [realSchurScalarOrbitMatrix] using
    realSchur_scalar_orbit_diagonal_coefficient T p.1.1 p.1.2
      (ne_of_gt p.2) (1 : ℝ)

#print axioms realSchur_scalar_orbit_det
end SpectralRadiusUpperTail
