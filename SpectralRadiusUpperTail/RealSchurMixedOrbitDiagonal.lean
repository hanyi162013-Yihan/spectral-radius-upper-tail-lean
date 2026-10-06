import SpectralRadiusUpperTail.MatrixSkewSingleCommutator
import SpectralRadiusUpperTail.RealSchurLowerDistanceOrder
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Scalar coordinates of a sequence of possibly different-sized Schur blocks. -/
abbrev RealSchurMixedCoord {m : ℕ} (s : Fin m → ℕ) :=
  Σ i : Fin m, Fin (s i)

/-- Matrix coordinates in the lower block indexed by `p`. -/
abbrev RealSchurMixedBridge {m : ℕ} (s : Fin m → ℕ)
    (p : RealSchurLowerIndex m) :=
  Fin (s p.1.1) × Fin (s p.1.2)

/-- All lower-block coordinates, with a fiber whose dimension depends on the
two block sizes. -/
abbrev RealSchurMixedOrbitIndex {m : ℕ} (s : Fin m → ℕ) :=
  Σ p : RealSchurLowerIndex m, RealSchurMixedBridge s p

/-- The elementary skew direction corresponding to one lower-block entry. -/
def realSchurMixedOrbitGenerator {m : ℕ} (s : Fin m → ℕ)
    (q : RealSchurMixedOrbitIndex s) :
    Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ :=
  let u : RealSchurMixedCoord s := ⟨q.1.1.1, q.2.1⟩
  let v : RealSchurMixedCoord s := ⟨q.1.1.2, q.2.2⟩
  Matrix.single u v (-1) + Matrix.single v u 1

/-- The angular derivative from skew directions to lower-block entries. -/
def realSchurMixedOrbitMatrix {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    Matrix (RealSchurMixedOrbitIndex s) (RealSchurMixedOrbitIndex s) ℝ :=
  fun p q =>
    let K := realSchurMixedOrbitGenerator s q
    (K*T-T*K) ⟨p.1.1.1,p.2.1⟩ ⟨p.1.1.2,p.2.2⟩

/-- The diagonal fiber is the Sylvester operator `D_i X - X D_j` in
entrywise coordinates. -/
def realSchurMixedSylvester {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (p : RealSchurLowerIndex m) :
    Matrix (RealSchurMixedBridge s p) (RealSchurMixedBridge s p) ℝ :=
  fun r z =>
    (if r.2=z.2 then T ⟨p.1.1,r.1⟩ ⟨p.1.1,z.1⟩ else 0) -
    (if r.1=z.1 then T ⟨p.1.2,z.2⟩ ⟨p.1.2,r.2⟩ else 0)

theorem realSchurMixedOrbitMatrix_diagonal {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (p : RealSchurLowerIndex m)
    (r z : RealSchurMixedBridge s p) :
    realSchurMixedOrbitMatrix s T ⟨p,r⟩ ⟨p,z⟩ =
      realSchurMixedSylvester s T p r z := by
  have hne : p.1.1 ≠ p.1.2 := ne_of_gt p.2
  unfold realSchurMixedOrbitMatrix realSchurMixedOrbitGenerator
    realSchurMixedSylvester
  rw [matrix_skew_single_commutator_apply]
  simp [hne, eq_comm]
  by_cases h1 : r.1 = z.1 <;> by_cases h2 : r.2 = z.2 <;>
    simp [h1, h2] <;> ring

#print axioms realSchurMixedOrbitMatrix_diagonal
end SpectralRadiusUpperTail
