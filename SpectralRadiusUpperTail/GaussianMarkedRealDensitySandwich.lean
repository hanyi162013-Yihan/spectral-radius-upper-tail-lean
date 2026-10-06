import SpectralRadiusUpperTail.GaussianCharpolyAbsoluteMomentExterior
import SpectralRadiusUpperTail.RealGinibreCoreDensity
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory

/-- The density predicted by the marked-real-eigenline Jacobian.  Its
identification with the *actual* Gaussian eigenvalue intensity is a separate
geometric change-of-variables problem. -/
noncomputable def gaussianMarkedRealDensity (n : ℕ) (r : ℝ) : ℝ :=
  realGinibreCoreDensity n r *
    ((∫ z : Fin (n-1) × Fin (n-1) → ℝ,
       |(Matrix.of z.curry).charpoly.eval (Real.sqrt (n : ℝ)*r)|
       ∂Measure.pi (fun _ => standardNormal)) /
      (Real.sqrt (n : ℝ)*r)^(n-1))

/-- The actual Gaussian determinant calculation traps the candidate density
within a polynomial factor of its explicit Gamma core, uniformly outside the
unit disk.  No eigenvalue counting formula is used here. -/
theorem gaussianMarkedRealDensity_sandwich
    (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : 1 ≤ r) :
    realGinibreCoreDensity n r ≤ gaussianMarkedRealDensity n r ∧
    gaussianMarkedRealDensity n r ≤
      ((n : ℝ)+1)/2 * realGinibreCoreDensity n r := by
  let x : ℝ := Real.sqrt (n : ℝ)*r
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hrpos : 0 < r := by linarith
  have hx : 0 < x := mul_pos (Real.sqrt_pos.2 hnR) hrpos
  have hxsq : x^2 = (n : ℝ)*r^2 := by
    dsimp [x]
    rw [mul_pow, Real.sq_sqrt hnR.le]
  have hscale : ((n-1 : ℕ) : ℝ) ≤ x^2 := by
    have hsub : ((n-1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
    have hrsq : 1 ≤ r^2 := by nlinarith
    rw [hxsq]
    nlinarith [mul_nonneg hnR.le (sub_nonneg.mpr hrsq)]
  obtain ⟨hl, hu⟩ :=
    gaussian_charpoly_absolute_moment_exterior_bound
      (ι := Fin (n-1)) x hx (by simpa using hscale)
  simp only [Fintype.card_fin] at hl hu
  have hpow : 0 < x^(n-1) := pow_pos hx _
  have hratio : 1 ≤
      (∫ z : Fin (n-1) × Fin (n-1) → ℝ,
        |(Matrix.of z.curry).charpoly.eval x|
          ∂Measure.pi (fun _ => standardNormal)) / x^(n-1) := by
    apply (le_div_iff₀ hpow).2
    simpa using hl
  have hratioUpper :
      (∫ z : Fin (n-1) × Fin (n-1) → ℝ,
        |(Matrix.of z.curry).charpoly.eval x|
          ∂Measure.pi (fun _ => standardNormal)) / x^(n-1) ≤
          ((n : ℝ)+1)/2 := by
    apply (div_le_iff₀ hpow).2
    have hcast : (((n-1 : ℕ) : ℝ)+2) = (n : ℝ)+1 := by
      have hn1 : 1 ≤ n := hn
      rw [Nat.cast_sub hn1]
      ring
    rw [hcast] at hu
    exact hu
  have hcore := realGinibreCoreDensity_pos n hn r hrpos
  dsimp [gaussianMarkedRealDensity]
  change realGinibreCoreDensity n r ≤
      realGinibreCoreDensity n r *
        ((∫ z : Fin (n-1) × Fin (n-1) → ℝ,
          |(Matrix.of z.curry).charpoly.eval x|
            ∂Measure.pi (fun _ => standardNormal)) / x^(n-1)) ∧
    realGinibreCoreDensity n r *
        ((∫ z : Fin (n-1) × Fin (n-1) → ℝ,
          |(Matrix.of z.curry).charpoly.eval x|
            ∂Measure.pi (fun _ => standardNormal)) / x^(n-1)) ≤
      ((n : ℝ)+1)/2 * realGinibreCoreDensity n r
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hratio hcore.le]
  · nlinarith [mul_le_mul_of_nonneg_left hratioUpper hcore.le]

#print axioms gaussianMarkedRealDensity_sandwich
end SpectralRadiusUpperTail
