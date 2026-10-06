import SpectralRadiusUpperTail.RealSchurMixedAngularPositive
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Resultant of two monic real quadratic polynomials with trace/determinant
data `(t,d)` and `(u,e)`. -/
def realQuadraticResultant (t d u e : ℝ) : ℝ :=
  (d-e)^2 + (t-u)*(t*e-u*d)

/-- A scalar block and a general real 2×2 block contribute the
characteristic polynomial evaluated at the scalar. -/
theorem realSchurRectangularSylvester_pair_scalar_general
    (A : Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ) :
    (realSchurRectangularSylvester A (Matrix.scalar (Fin 1) a)).det =
      a^2-a*A.trace+A.det := by
  let f : Fin 2 × Fin 1 ≃ Fin 2 :=
    (finProdFinEquiv : Fin 2 × Fin 1 ≃ Fin (2*1))
  have hM : Matrix.reindex f f
      (realSchurRectangularSylvester A (Matrix.scalar (Fin 1) a)) =
      A - Matrix.scalar (Fin 2) a := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [f, finProdFinEquiv, Fin.divNat, Fin.modNat,
        realSchurRectangularSylvester, Matrix.scalar, Matrix.sub_apply]
  calc
    _ = (Matrix.reindex f f
      (realSchurRectangularSylvester A (Matrix.scalar (Fin 1) a))).det :=
      (Matrix.det_reindex_self f _).symm
    _ = (A - Matrix.scalar (Fin 2) a).det := congrArg Matrix.det hM
    _ = a^2-a*A.trace+A.det := by
      simp [Matrix.det_fin_two, Matrix.trace, Matrix.scalar,
        Matrix.sub_apply, Fin.sum_univ_two]
      ring

theorem realSchurRectangularSylvester_scalar_pair_general
    (a : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (realSchurRectangularSylvester (Matrix.scalar (Fin 1) a) A).det =
      a^2-a*A.trace+A.det := by
  let f : Fin 1 × Fin 2 ≃ Fin 2 :=
    (finProdFinEquiv : Fin 1 × Fin 2 ≃ Fin (1*2))
  have hM : Matrix.reindex f f
      (realSchurRectangularSylvester (Matrix.scalar (Fin 1) a) A) =
      (Matrix.scalar (Fin 2) a - A)ᵀ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [f, finProdFinEquiv, Fin.divNat, Fin.modNat,
        realSchurRectangularSylvester, Matrix.scalar,
        Matrix.sub_apply, Matrix.transpose_apply]
  calc
    _ = (Matrix.reindex f f
      (realSchurRectangularSylvester (Matrix.scalar (Fin 1) a) A)).det :=
      (Matrix.det_reindex_self f _).symm
    _ = ((Matrix.scalar (Fin 2) a - A)ᵀ).det := congrArg Matrix.det hM
    _ = a^2-a*A.trace+A.det := by
      rw [Matrix.det_transpose]
      simp [Matrix.det_fin_two, Matrix.trace, Matrix.scalar,
        Matrix.sub_apply, Fin.sum_univ_two]
      ring

/-- Explicit four-dimensional resultant calculation for two arbitrary
real 2×2 diagonal blocks. -/
theorem realSylvester_two_by_two_det_explicit
    (a b c d u v w z : ℝ) :
    (Matrix.det (!![a-u, -w, b, 0;
      -v, a-z, 0, b;
      c, 0, d-u, -w;
      0, c, -v, d-z] : Matrix (Fin 4) (Fin 4) ℝ)) =
        realQuadraticResultant (a+d) (a*d-b*c) (u+z) (u*z-v*w) := by
  simp [realQuadraticResultant, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ]
  have h12 : Fin.succAbove (1 : Fin 4) (2 : Fin 3) = 3 := by decide
  have h22 : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 := by decide
  simp [h12, h22] at *
  ring

/-- For arbitrary 2×2 blocks, the Sylvester determinant is the
resultant of their characteristic polynomials, expressed through trace
and determinant. No canonical pair-block shape is needed. -/
theorem realSchurRectangularSylvester_pair_pair_general
    (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    (realSchurRectangularSylvester A B).det =
      realQuadraticResultant A.trace A.det B.trace B.det := by
  let f : Fin 2 × Fin 2 ≃ Fin 4 :=
    (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2*2))
  have hM : Matrix.reindex f f (realSchurRectangularSylvester A B) =
      !![A 0 0-B 0 0, -B 1 0, A 0 1, 0;
         -B 0 1, A 0 0-B 1 1, 0, A 0 1;
         A 1 0, 0, A 1 1-B 0 0, -B 1 0;
         0, A 1 0, -B 0 1, A 1 1-B 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [f, finProdFinEquiv, Fin.divNat, Fin.modNat,
        realSchurRectangularSylvester]
  calc
    _ = (Matrix.reindex f f (realSchurRectangularSylvester A B)).det :=
      (Matrix.det_reindex_self f _).symm
    _ = (Matrix.det (!![A 0 0-B 0 0, -B 1 0, A 0 1, 0;
         -B 0 1, A 0 0-B 1 1, 0, A 0 1;
         A 1 0, 0, A 1 1-B 0 0, -B 1 0;
         0, A 1 0, -B 0 1, A 1 1-B 1 1] :
           Matrix (Fin 4) (Fin 4) ℝ)) := congrArg Matrix.det hM
    _ = realQuadraticResultant A.trace A.det B.trace B.det := by
      rw [realSylvester_two_by_two_det_explicit]
      simp [Matrix.trace, Matrix.det_fin_two, Fin.sum_univ_two]

#print axioms realSchurRectangularSylvester_pair_scalar_general
#print axioms realSchurRectangularSylvester_scalar_pair_general
#print axioms realSchurRectangularSylvester_pair_pair_general
end SpectralRadiusUpperTail
