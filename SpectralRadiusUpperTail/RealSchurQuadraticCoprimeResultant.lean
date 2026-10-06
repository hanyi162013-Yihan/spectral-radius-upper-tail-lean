import SpectralRadiusUpperTail.RealSchurMixedResultant
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Polynomial

/-- The monic quadratic with prescribed trace and determinant. -/
noncomputable def realSchurMonicQuadratic (t d : ℝ) : ℝ[X] :=
  X ^ 2 - C t * X + C d

theorem realSchurMonicQuadratic_eval (t d r : ℝ) :
    (realSchurMonicQuadratic t d).eval r = r^2-t*r+d := by
  simp [realSchurMonicQuadratic]

theorem realSchurMonicQuadratic_degree (t d : ℝ) :
    (realSchurMonicQuadratic t d).degree = 2 := by
  unfold realSchurMonicQuadratic
  compute_degree!

/-- Coprime monic quadratics have a nonzero explicit resultant. -/
theorem realQuadraticResultant_ne_zero_of_isCoprime
    (t d u e : ℝ)
    (hcop : IsCoprime (realSchurMonicQuadratic t d)
      (realSchurMonicQuadratic u e)) :
    realQuadraticResultant t d u e ≠ 0 := by
  intro hzero
  by_cases htrace : t = u
  · have hdet : d = e := by
      unfold realQuadraticResultant at hzero
      rw [htrace] at hzero
      nlinarith [sq_nonneg (d-e)]
    have hself : IsCoprime (realSchurMonicQuadratic t d)
        (realSchurMonicQuadratic t d) := by
      simpa [htrace, hdet] using hcop
    have hunit := isCoprime_self.mp hself
    have hdeg0 := Polynomial.isUnit_iff_degree_eq_zero.mp hunit
    rw [realSchurMonicQuadratic_degree] at hdeg0
    norm_num at hdeg0
  · let r : ℝ := (d-e)/(t-u)
    have hden : t-u ≠ 0 := sub_ne_zero.mpr htrace
    have hidentity :
        (d-e)^2-t*(d-e)*(t-u)+d*(t-u)^2 =
          realQuadraticResultant t d u e := by
      unfold realQuadraticResultant
      ring
    have hnum : (d-e)^2-t*(d-e)*(t-u)+d*(t-u)^2 = 0 := by
      rw [hidentity]
      exact hzero
    have hf : r^2-t*r+d = 0 := by
      dsimp [r]
      field_simp [hden]
      nlinarith [hnum]
    have hdiff : -(t-u)*r+(d-e) = 0 := by
      dsimp [r]
      field_simp [hden]
      ring
    have hg : r^2-u*r+e = 0 := by
      nlinarith [hf, hdiff]
    rcases aeval_ne_zero_of_isCoprime hcop r with hn | hn
    · have heval : (realSchurMonicQuadratic t d).eval r = 0 := by
        rw [realSchurMonicQuadratic_eval]
        exact hf
      exact hn (by simpa using heval)
    · have heval : (realSchurMonicQuadratic u e).eval r = 0 := by
        rw [realSchurMonicQuadratic_eval]
        exact hg
      exact hn (by simpa using heval)

/-- Disjoint characteristic polynomials make the 2×2/2×2
matrix Sylvester bridge invertible. -/
theorem realSchurRectangularSylvester_pair_pair_ne_zero_of_coprime
    (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hcop : IsCoprime A.charpoly B.charpoly) :
    (realSchurRectangularSylvester A B).det ≠ 0 := by
  rw [realSchurRectangularSylvester_pair_pair_general]
  apply realQuadraticResultant_ne_zero_of_isCoprime
  simpa [realSchurMonicQuadratic, Matrix.charpoly_fin_two] using hcop

#print axioms realQuadraticResultant_ne_zero_of_isCoprime
#print axioms realSchurRectangularSylvester_pair_pair_ne_zero_of_coprime
end SpectralRadiusUpperTail
