import SpectralRadiusUpperTail.GaussianMarkedRealDensitySandwich
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- The constant left after the marked-real candidate's radial power is
cancelled against the leading power of the Gaussian determinant. -/
noncomputable def gaussianMarkedRealJacobianPrefactor (n : ℕ) : ℝ :=
  (((n : ℝ)/2)^((n : ℝ)/2)) /
    ((Real.sqrt (n : ℝ))^(n-1)*Real.Gamma ((n : ℝ)/2))

/-- An exact normalization bridge from the Gamma-core ratio used for the
tail proof to the shifted-determinant factor used by marked-eigenline
coordinates. This identity does not assert an eigenvalue count formula. -/
theorem gaussianMarkedRealDensity_eq_prefactor_moment
    (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 0 < r) :
    gaussianMarkedRealDensity n r =
      gaussianMarkedRealJacobianPrefactor n *
        Real.exp (-(n : ℝ)*r^2/2) *
        (∫ z : Fin (n-1) × Fin (n-1) → ℝ,
          |(Matrix.of z.curry).charpoly.eval (Real.sqrt (n : ℝ)*r)|
            ∂Measure.pi (fun _ => standardNormal)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hs : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 hnR).ne'
  have hg : Real.Gamma ((n : ℝ)/2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hpow : r^((n : ℝ)-1) = r^(n-1) := by
    have hn1 : 1 ≤ n := hn
    rw [show (n : ℝ)-1 = ((n-1 : ℕ) : ℝ) by
      rw [Nat.cast_sub hn1]; norm_num]
    exact Real.rpow_natCast r (n-1)
  unfold gaussianMarkedRealDensity realGinibreCoreDensity
    gaussianMarkedRealJacobianPrefactor
  rw [hpow, mul_pow]
  field_simp [hr.ne', hs, hg]

/-- The prefactor is exactly the sphere-area normalization divided by two
in the standard marked-eigenline Kac--Rice formula. -/
theorem gaussianMarkedRealJacobianPrefactor_eq_kacRice
    (n : ℕ) (hn : 0 < n) :
    gaussianMarkedRealJacobianPrefactor n =
      Real.sqrt (n : ℝ) * (2 : ℝ)^(-((n : ℝ)/2)) /
        Real.Gamma ((n : ℝ)/2) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hnR).ne'
  have htwo : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hg : Real.Gamma ((n : ℝ)/2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hnum : ((n : ℝ)/2)^((n : ℝ)/2) =
      (Real.sqrt (n : ℝ)/Real.sqrt 2)^n := by
    calc
      ((n : ℝ)/2)^((n : ℝ)/2) =
          (Real.sqrt ((n : ℝ)/2))^((n : ℝ)) :=
        Real.rpow_div_two_eq_sqrt (n : ℝ) (by positivity)
      _ = (Real.sqrt (n : ℝ)/Real.sqrt 2)^((n : ℝ)) := by
        rw [Real.sqrt_div hnR.le]
      _ = (Real.sqrt (n : ℝ)/Real.sqrt 2)^n :=
        Real.rpow_natCast _ _
  have hrootpow : (Real.sqrt (n : ℝ))^n =
      (Real.sqrt (n : ℝ))^(n-1)*Real.sqrt (n : ℝ) := by
    calc
      _ = (Real.sqrt (n : ℝ))^(n-1+1) := by
        rw [Nat.sub_add_cancel hn]
      _ = _ := pow_succ _ _
  have htwopow : (Real.sqrt (2 : ℝ))^n =
      (2 : ℝ)^((n : ℝ)/2) := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_div_two_eq_sqrt (n : ℝ) (by norm_num : (0 : ℝ) ≤ 2)).symm
  have hneg : (2 : ℝ)^(-((n : ℝ)/2)) =
      1/(Real.sqrt (2 : ℝ))^n := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← htwopow]
    simp only [one_div]
  unfold gaussianMarkedRealJacobianPrefactor
  rw [hnum, div_pow, hrootpow, hneg]
  field_simp [hs, htwo, hg]

/-- The marked-real candidate is exactly the predicted scaled Kac--Rice
integrand, with its sphere-area factor shown explicitly. This remains a
candidate until the global marked-eigenline formula is proved. -/
theorem gaussianMarkedRealDensity_eq_kacRice_moment
    (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 0 < r) :
    gaussianMarkedRealDensity n r =
      (Real.sqrt (n : ℝ) * (2 : ℝ)^(-((n : ℝ)/2)) /
        Real.Gamma ((n : ℝ)/2)) *
        Real.exp (-(n : ℝ)*r^2/2) *
        (∫ z : Fin (n-1) × Fin (n-1) → ℝ,
          |(Matrix.of z.curry).charpoly.eval (Real.sqrt (n : ℝ)*r)|
            ∂Measure.pi (fun _ => standardNormal)) := by
  rw [gaussianMarkedRealDensity_eq_prefactor_moment n hn r hr,
    gaussianMarkedRealJacobianPrefactor_eq_kacRice n hn]

#print axioms gaussianMarkedRealDensity_eq_prefactor_moment
#print axioms gaussianMarkedRealJacobianPrefactor_eq_kacRice
#print axioms gaussianMarkedRealDensity_eq_kacRice_moment
end SpectralRadiusUpperTail
