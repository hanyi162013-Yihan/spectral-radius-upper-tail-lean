import SpectralRadiusUpperTail.RealSchurJacobianPairFactors
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- Polynomial coordinates for a real Schur conjugate-pair block:
`u = bc` is the squared imaginary part and `s = (b-c)^2` is the
squared departure from a normal block. -/
def realSchurPairCoordinates (b c : ℝ) : ℝ × ℝ :=
  (b*c, (b-c)^2)

/-- The two elementary algebraic relations used to separate the Gaussian
weight in the pair block. -/
theorem realSchur_pair_coordinates_energy (b c : ℝ) :
    b^2+c^2 = (realSchurPairCoordinates b c).2 +
      2*(realSchurPairCoordinates b c).1 := by
  simp [realSchurPairCoordinates]
  ring

theorem realSchur_pair_coordinates_sum_sq (b c : ℝ) :
    (b+c)^2 = (realSchurPairCoordinates b c).2 +
      4*(realSchurPairCoordinates b c).1 := by
  simp [realSchurPairCoordinates]
  ring

/-- Differential of `(b,c) ↦ (bc,(b-c)^2)` in entry coordinates. -/
def realSchurPairCoordinateDerivative (b c : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![c, b; 2*(b-c), -2*(b-c)]

/-- Exact first-order expansion, including its quadratic remainder. This
identifies the displayed matrix as the derivative of the coordinate map. -/
theorem realSchur_pair_coordinates_increment (b c h k : ℝ) :
    ![(realSchurPairCoordinates (b+h) (c+k)).1 -
        (realSchurPairCoordinates b c).1,
      (realSchurPairCoordinates (b+h) (c+k)).2 -
        (realSchurPairCoordinates b c).2] =
      (realSchurPairCoordinateDerivative b c).mulVec ![h,k] +
        ![h*k,(h-k)^2] := by
  ext i
  fin_cases i <;>
    simp [realSchurPairCoordinates, realSchurPairCoordinateDerivative,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    ring

theorem realSchur_pair_coordinate_derivative_det (b c : ℝ) :
    Matrix.det (realSchurPairCoordinateDerivative b c) =
      -2*(b-c)*(b+c) := by
  simp [realSchurPairCoordinateDerivative, Matrix.det_fin_two]
  ring

theorem realSchur_pair_coordinate_derivative_ne_zero
    (b c : ℝ) (hbc : b ≠ c) (hsum : b+c ≠ 0) :
    Matrix.det (realSchurPairCoordinateDerivative b c) ≠ 0 := by
  rw [realSchur_pair_coordinate_derivative_det]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hbc)) hsum

/-- An equivalent form of the pair energy when the spectral imaginary part
is prescribed by `bc=y²`. -/
theorem realSchur_pair_energy_of_spectrum (b c y : ℝ) (hbc : b*c = y^2) :
    b^2+c^2 = (b-c)^2+2*y^2 := by
  nlinarith [realSchur_pair_coordinates_energy b c]

/-- The Gaussian weight of one conjugate-pair block separates into the
spectral weight and the squared-gap weight. This is an equality of
functions, before any Schur change-of-variables claim. -/
theorem realSchur_pair_gaussian_weight (n x b c y : ℝ)
    (hbc : b*c = y^2) :
    Real.exp (-(n/2)*(2*x^2+b^2+c^2)) =
      Real.exp (-n*(x^2+y^2)) *
        Real.exp (-(n/2)*(b-c)^2) := by
  rw [← Real.exp_add]
  congr 1
  have henergy : 2*x^2+b^2+c^2 =
      2*x^2+((b-c)^2+2*y^2) := by
    linear_combination realSchur_pair_energy_of_spectrum b c y hbc
  rw [henergy]
  ring

/-- On the usual positive Schur chart, the coordinate determinant has
the explicit square-root form appearing in the gap density. -/
theorem realSchur_pair_coordinate_jacobian_chart
    (b c : ℝ) (hb : 0 < b) (hc : 0 < c) (hcb : c < b) :
    |Matrix.det (realSchurPairCoordinateDerivative b c)| =
      2*(b-c)*Real.sqrt ((realSchurPairCoordinates b c).2 +
        4*(realSchurPairCoordinates b c).1) := by
  rw [realSchur_pair_coordinate_derivative_det]
  have hdiff : 0 < b-c := sub_pos.mpr hcb
  have hsum : 0 ≤ b+c := by linarith
  have hsqrt : Real.sqrt ((realSchurPairCoordinates b c).2 +
      4*(realSchurPairCoordinates b c).1) = b+c := by
    rw [← realSchur_pair_coordinates_sum_sq]
    exact Real.sqrt_sq_eq_abs (b+c) |>.trans (abs_of_nonneg hsum)
  rw [hsqrt]
  rw [abs_of_nonpos (by nlinarith : -2*(b-c)*(b+c) ≤ 0)]
  ring

#print axioms realSchur_pair_coordinates_energy
#print axioms realSchur_pair_coordinates_sum_sq
#print axioms realSchur_pair_coordinate_derivative_det
#print axioms realSchur_pair_coordinates_increment
#print axioms realSchur_pair_coordinate_derivative_ne_zero
#print axioms realSchur_pair_energy_of_spectrum
#print axioms realSchur_pair_gaussian_weight
#print axioms realSchur_pair_coordinate_jacobian_chart
end SpectralRadiusUpperTail
