import SpectralRadiusUpperTail.RealSchurMixedChartPolynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Factor the complexification of the real quadratic belonging to a
nonreal conjugate pair. -/
private theorem realSchurMixed_complex_pair_factor (x y : ℝ) :
    (Polynomial.X : Polynomial ℂ)^2 -
        Polynomial.C (2*(x : ℂ))*Polynomial.X +
          Polynomial.C ((x : ℂ)^2+(y : ℂ)^2) =
      (Polynomial.X-Polynomial.C ((x : ℂ)+(y : ℂ)*Complex.I)) *
        (Polynomial.X-Polynomial.C ((x : ℂ)-(y : ℂ)*Complex.I)) := by
  let u : ℂ := (x : ℂ)+(y : ℂ)*Complex.I
  let v : ℂ := (x : ℂ)-(y : ℂ)*Complex.I
  have hs : u+v = 2*(x : ℂ) := by dsimp [u,v]; ring
  have hp : u*v = (x : ℂ)^2+(y : ℂ)^2 := by
    calc
      u*v = (x : ℂ)^2-(y : ℂ)^2*Complex.I^2 := by dsimp [u,v]; ring
      _ = _ := by rw [Complex.I_sq]; ring
  calc
    _ = Polynomial.X^2-Polynomial.C (u+v)*Polynomial.X+
      Polynomial.C (u*v) := by rw [hs,hp]
    _ = (Polynomial.X-Polynomial.C u)*(Polynomial.X-Polynomial.C v) := by
      simp only [map_add, map_mul]
      ring
    _ = _ := rfl

/-- The prescribed complex roots of one admissible real-Schur block,
including the conjugate partner and algebraic multiplicity. -/
noncomputable def RealSchurChartBlock.complexRoots :
    RealSchurChartBlock → Multiset ℂ
  | .scalar a => {(a : ℂ)}
  | .pair x _ _ y _ _ =>
      ({(x : ℂ)+(y : ℂ)*Complex.I} : Multiset ℂ) +
        {(x : ℂ)-(y : ℂ)*Complex.I}

theorem RealSchurChartBlock.aroots_eq_complexRoots
    (B : RealSchurChartBlock) :
    B.matrix.charpoly.aroots ℂ = B.complexRoots := by
  cases B with
  | scalar a =>
    rw [RealSchurChartBlock.charpoly_eq_polynomial]
    change (Polynomial.X-Polynomial.C a).aroots ℂ = {(a : ℂ)}
    exact Polynomial.aroots_X_sub_C a
  | pair x b c y hbc hy =>
    rw [RealSchurChartBlock.charpoly_eq_polynomial]
    change (Polynomial.X^2 - Polynomial.C (2*x)*Polynomial.X +
      Polynomial.C (x^2+y^2)).aroots ℂ =
        ({(x : ℂ)+(y : ℂ)*Complex.I} : Multiset ℂ) +
          {(x : ℂ)-(y : ℂ)*Complex.I}
    rw [Polynomial.aroots_def]
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    norm_num
    have hfactor :
        (Polynomial.X : Polynomial ℂ)^2 -
          Polynomial.C 2 * Polynomial.C (x : ℂ) * Polynomial.X +
            (Polynomial.C (x : ℂ)^2 + Polynomial.C (y : ℂ)^2) =
        (Polynomial.X-Polynomial.C ((x : ℂ)+(y : ℂ)*Complex.I)) *
          (Polynomial.X-Polynomial.C ((x : ℂ)-(y : ℂ)*Complex.I)) := by
      simpa only [map_add, map_mul, map_pow] using
        realSchurMixed_complex_pair_factor x y
    rw [hfactor]
    rw [Polynomial.roots_mul
      (mul_ne_zero
        (Polynomial.X_sub_C_ne_zero _)
        (Polynomial.X_sub_C_ne_zero _)),
      Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
    simp

#print axioms RealSchurChartBlock.aroots_eq_complexRoots
end SpectralRadiusUpperTail
