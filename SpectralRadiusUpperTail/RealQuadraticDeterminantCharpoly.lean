import SpectralRadiusUpperTail.ComplexMatrixQuadraticFactorization
import SpectralRadiusUpperTail.RealCharpolyConjugation
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The real determinant appearing in the nonreal Schur-pair Jacobian is
the squared modulus of a complex characteristic polynomial. -/
theorem real_quadratic_det_eq_charpoly_normSq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (x y : ℝ) :
    ((M - x • 1)^2 + y^2 • 1).det =
      Complex.normSq
        ((M.map Complex.ofRealHom).charpoly.eval
          ((x : ℂ) + (y : ℂ)*Complex.I)) := by
  classical
  let C : Matrix ι ι ℂ := M.map Complex.ofRealHom
  let D : Matrix ι ι ℝ := M - x • 1
  let t : ℂ := (y : ℂ)*Complex.I
  let w : ℂ := (x : ℂ)+t
  have ht : t^2 = -((y^2 : ℝ) : ℂ) := by
    dsimp [t]
    rw [mul_pow, Complex.I_sq]
    norm_num
  have hD : D.map Complex.ofRealHom = C - (x : ℂ) • 1 := by
    ext i j
    by_cases hij : i = j <;>
      simp [D, C, Matrix.sub_apply, Matrix.smul_apply, hij]
  have hY : (y^2 • (1 : Matrix ι ι ℝ)).map Complex.ofRealHom =
      (y^2 : ℂ) • (1 : Matrix ι ι ℂ) := by
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.smul_apply, hij]
  have hQ : ((D^2 + y^2 • 1).map Complex.ofRealHom) =
      (C - (x : ℂ) • 1)^2 + (y^2 : ℂ) • 1 := by
    change Complex.ofRealHom.mapMatrix (D^2 + y^2 • 1) = _
    rw [map_add, map_pow, RingHom.mapMatrix_apply, hD]
    change (C - (x : ℂ) • 1)^2 +
      (y^2 • (1 : Matrix ι ι ℝ)).map Complex.ofRealHom = _
    rw [hY]
  have hneg : ((x : ℂ) • (1 : Matrix ι ι ℂ) - C)^2 =
      (C - (x : ℂ) • 1)^2 := by
    have he : (x : ℂ) • (1 : Matrix ι ι ℂ) - C =
        -(C - (x : ℂ) • 1) := by abel
    calc
      _ = (-(C - (x : ℂ) • 1))^2 := congrArg (fun B => B^2) he
      _ = _ := neg_sq _
  have hfac :
      (w • (1 : Matrix ι ι ℂ) - C) *
        (((x : ℂ)-t) • 1 - C) =
        (D^2 + y^2 • 1).map Complex.ofRealHom := by
    calc
      _ = ((x : ℂ) • (1 : Matrix ι ι ℂ) - C)^2 - t^2 • 1 := by
        simpa only [w] using
          complex_matrix_conjugate_shift_factorization C (x : ℂ) t
      _ = (C - (x : ℂ) • 1)^2 + (y^2 : ℂ) • 1 := by
        rw [hneg, ht, neg_smul]
        push_cast
        abel
      _ = _ := hQ.symm
  have hwt : star w = (x : ℂ)-t := by
    dsimp [w, t]
    simp
    ring
  have hconj := real_matrix_complex_charpoly_eval_conj M w
  change star (C.charpoly.eval w) = C.charpoly.eval (star w) at hconj
  rw [hwt] at hconj
  have hscalar (z : ℂ) :
      Matrix.scalar ι z = z • (1 : Matrix ι ι ℂ) := by
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.scalar_apply, Matrix.smul_apply, hij]
  have heval (z : ℂ) : C.charpoly.eval z = (z • 1 - C).det := by
    rw [Matrix.eval_charpoly, hscalar]
  have hprod := congrArg Matrix.det hfac
  rw [Matrix.det_mul, ← heval, ← heval] at hprod
  have hmapdet :
      (((D^2 + y^2 • 1).det : ℝ) : ℂ) =
        ((D^2 + y^2 • 1).map Complex.ofRealHom).det := by
    change Complex.ofRealHom (D^2 + y^2 • 1).det = _
    exact RingHom.map_det Complex.ofRealHom _
  have hnorm :
      ((Complex.normSq (C.charpoly.eval w) : ℝ) : ℂ) =
        C.charpoly.eval w * star (C.charpoly.eval w) := by
    simpa only [Complex.star_def] using
      (Complex.mul_conj (C.charpoly.eval w)).symm
  apply Complex.ofReal_injective
  change (((D^2 + y^2 • 1).det : ℝ) : ℂ) =
    ((Complex.normSq (C.charpoly.eval w) : ℝ) : ℂ)
  rw [hmapdet, hnorm, hconj]
  exact hprod.symm

#print axioms real_quadratic_det_eq_charpoly_normSq
end SpectralRadiusUpperTail
