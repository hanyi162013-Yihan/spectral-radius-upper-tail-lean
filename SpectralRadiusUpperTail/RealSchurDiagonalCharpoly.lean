import SpectralRadiusUpperTail.RealSchurBlockData
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

lemma realSchurBlock_charpoly (x b c : ℝ) :
    (realSchurBlock x b c).charpoly =
      Polynomial.X^2 - Polynomial.C (2*x)*Polynomial.X +
        Polynomial.C (x^2+b*c) := by
  rw [Matrix.charpoly_fin_two]
  simp only [Matrix.trace_fin_two, Matrix.det_fin_two]
  simp [realSchurBlock]
  have htwo : Polynomial.C (2 : ℝ) = (2 : Polynomial ℝ) := by
    calc
      Polynomial.C (2 : ℝ) = Polynomial.C ((1 : ℝ)+1) := by norm_num
      _ = Polynomial.C (1 : ℝ)+Polynomial.C (1 : ℝ) := map_add _ _ _
      _ = (2 : Polynomial ℝ) := by norm_num
  rw [htwo]
  ring

lemma schurGapPowerBlock_charpoly (x y s : ℝ) :
    (schurGapPowerBlock x y 1 s).charpoly =
      Polynomial.X^2 - Polynomial.C (2*x)*Polynomial.X +
        Polynomial.C (x^2+y^2) := by
  rw [schurGapPowerBlock, pow_one,
    realSchurBlock_charpoly, schurGapBlock_product]

theorem realSchurDataPower_charpoly (B : RealSchurBlockData) (s : ℝ) :
    (realSchurDataPower B 1 s).charpoly =
      match B with
      | .real x => Polynomial.X * (Polynomial.X - Polynomial.C x)
      | .pair x y => Polynomial.X^2 - Polynomial.C (2*x)*Polynomial.X +
          Polynomial.C (x^2+y^2) := by
  cases B with
  | real x =>
    rw [Matrix.charpoly_fin_two]
    simp [realSchurDataPower, Matrix.trace_fin_two, Matrix.det_fin_two]
    ring
  | pair x y =>
    exact schurGapPowerBlock_charpoly x y s

#print axioms realSchurDataPower_charpoly
end SpectralRadiusUpperTail
