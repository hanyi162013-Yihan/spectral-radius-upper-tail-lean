import SpectralRadiusUpperTail.GaussianComplexCharpolyMomentCardinality
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

/-- Outside the square-root dimension scale, the nonreal shifted determinant
moment lies within a polynomial factor of its leading monomial. -/
theorem gaussian_real_complex_charpoly_exterior_bounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ℂ) (hscale : (Fintype.card ι : ℝ) ≤ Complex.normSq w) :
    (Complex.normSq w)^(Fintype.card ι) ≤
      (∫ z : ι × ι → ℝ,
        Complex.normSq
          (((Matrix.of z.curry).map Complex.ofRealHom).charpoly.eval w)
        ∂Measure.pi (fun _ => standardNormal)) ∧
    (∫ z : ι × ι → ℝ,
        Complex.normSq
          (((Matrix.of z.curry).map Complex.ofRealHom).charpoly.eval w)
        ∂Measure.pi (fun _ => standardNormal)) ≤
      ((Fintype.card ι : ℝ)+1) *
        (Complex.normSq w)^(Fintype.card ι) := by
  classical
  let m := Fintype.card ι
  let q := Complex.normSq w
  rw [gaussian_real_complex_charpoly_second_moment_cardinality]
  constructor
  · have h := Finset.single_le_sum
        (f := fun k : ℕ =>
          (((m.choose k * k.factorial : ℕ) : ℝ)) * q^(m-k))
        (s := Finset.range (m+1)) (a := 0)
        (fun k hk => mul_nonneg
          (Nat.cast_nonneg (m.choose k * k.factorial))
          (pow_nonneg (Complex.normSq_nonneg w) (m-k)))
        (Finset.mem_range.mpr (Nat.zero_lt_succ m))
    simpa [m, q] using h
  · calc
      (∑ k ∈ Finset.range (m+1),
        (((m.choose k * k.factorial : ℕ) : ℝ)) * q^(m-k)) ≤
          ∑ _k ∈ Finset.range (m+1), q^m := by
        apply Finset.sum_le_sum
        intro k hk
        have hnat : m.choose k * k.factorial ≤ m^k := by
          rw [Nat.mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
          exact Nat.descFactorial_le_pow m k
        have hcoef : (((m.choose k * k.factorial : ℕ) : ℝ)) ≤ (m : ℝ)^k := by
          exact_mod_cast hnat
        have hpow : (m : ℝ)^k ≤ q^k :=
          pow_le_pow_left₀ (Nat.cast_nonneg m) hscale k
        have hnonneg : 0 ≤ q^(m-k) :=
          pow_nonneg (Complex.normSq_nonneg w) _
        have hmul := mul_le_mul_of_nonneg_right (hcoef.trans hpow) hnonneg
        calc
          _ ≤ q^k * q^(m-k) := hmul
          _ = q^m := by
            rw [← pow_add]
            congr 1
            have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            omega
      _ = ((m : ℝ)+1)*q^m := by
        simp [nsmul_eq_mul, Nat.cast_add]

#print axioms gaussian_real_complex_charpoly_exterior_bounds
end SpectralRadiusUpperTail
