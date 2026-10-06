import SpectralRadiusUpperTail.RealSchurMixedSylvesterFactors
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A scalar or admissible conjugate-pair diagonal block, carrying both its
real matrix coordinates and its eigenvalue coordinates. -/
inductive RealSchurChartBlock where
  | scalar (a : ℝ)
  | pair (x b c y : ℝ) (hbc : b*c = y^2) (hy : 0 < y)

def RealSchurChartBlock.size : RealSchurChartBlock → ℕ
  | .scalar _ => 1
  | .pair .. => 2

def RealSchurChartBlock.matrix (B : RealSchurChartBlock) :
    Matrix (Fin B.size) (Fin B.size) ℝ :=
  match B with
  | .scalar a => Matrix.scalar (Fin 1) a
  | .pair x b c _ _ _ => realSchurBlock x b c

def RealSchurChartBlock.data : RealSchurChartBlock → RealSchurBlockData
  | .scalar a => .real a
  | .pair x _ _ y _ _ => .pair x y

theorem RealSchurChartBlock.size_pos (B : RealSchurChartBlock) :
    0 < B.size := by
  cases B <;> simp [RealSchurChartBlock.size]

/-- Each rectangular Sylvester determinant has exactly the expected local
spectral-gap absolute value, for all four block-type combinations. -/
theorem realSchurChartBlock_sylvester_abs
    (A B : RealSchurChartBlock) :
    |(realSchurRectangularSylvester A.matrix B.matrix).det| =
      realSchurSpectralGap A.data B.data := by
  cases A with
  | scalar a =>
    cases B with
    | scalar u =>
      change |(realSchurRectangularSylvester
        (Matrix.scalar (Fin 1) a) (Matrix.scalar (Fin 1) u)).det| = |a-u|
      exact congrArg abs (realSchurRectangularSylvester_scalar_scalar a u)
    | pair x b c y hbc hy =>
      change |(realSchurRectangularSylvester
        (Matrix.scalar (Fin 1) a) (realSchurBlock x b c)).det| =
        (a-x)^2+y^2
      rw [realSchurRectangularSylvester_scalar_pair, hbc]
      rw [abs_of_nonneg (by positivity)]
  | pair x b c y hbc hy =>
    cases B with
    | scalar a =>
      change |(realSchurRectangularSylvester
        (realSchurBlock x b c) (Matrix.scalar (Fin 1) a)).det| =
          (a-x)^2+y^2
      rw [realSchurRectangularSylvester_pair_scalar, hbc]
      rw [abs_of_nonneg (by positivity)]
      ring
    | pair u d e v hde hv =>
      change |(realSchurRectangularSylvester
        (realSchurBlock x b c) (realSchurBlock u d e)).det| =
          ((x-u)^2+(y-v)^2)*((x-u)^2+(y+v)^2)
      rw [realSchurRectangularSylvester_pair_pair,
        realSchur_pair_pair_factor x b c u d e y v hbc hde]
      rw [abs_of_nonneg (by positivity)]

/-- The absolute angular Jacobian for a whole mixed real-Schur pattern is
the product of its scalar/scalar, scalar/pair and pair/pair spectral gaps.
This is the algebraic Jacobian, before global chart multiplicity and the
Lebesgue change of variables. -/
theorem realSchurChartBlock_orbit_abs_det
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b) :
    |(realSchurMixedOrbitMatrix (fun i => (B i).size) T).det| =
      ∏ p : RealSchurLowerIndex m,
        realSchurSpectralGap (B p.1.1).data (B p.1.2).data := by
  let s := fun i : Fin m => (B i).size
  have hs : ∀ i, 0 < s i := fun i => (B i).size_pos
  rw [realSchurMixedOrbitMatrix_det s hs T hT,
    Finset.abs_prod]
  apply Finset.prod_congr rfl
  intro p _
  rw [realSchurMixedSylvester_eq_rectangular s T
    (fun i => (B i).matrix) hdiag p]
  exact realSchurChartBlock_sylvester_abs (B p.1.1) (B p.1.2)

#print axioms realSchurChartBlock_orbit_abs_det
end SpectralRadiusUpperTail
