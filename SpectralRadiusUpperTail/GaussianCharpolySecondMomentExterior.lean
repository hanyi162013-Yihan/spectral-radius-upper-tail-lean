import SpectralRadiusUpperTail.GaussianCharpolyMomentCardinality
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

/-- Outside the square-root dimension scale, every cardinality term in
the exact shifted-determinant second moment is bounded by its leading
power. The polynomial prefactor is harmless at speed `n`. -/
theorem gaussian_charpoly_second_moment_exterior_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ℝ) (hx : 0 ≤ x) (hscale : (Fintype.card ι : ℝ) ≤ x^2) :
    (∫ z : ι × ι → ℝ,
      ((Matrix.of z.curry).charpoly.eval x)^2
      ∂Measure.pi (fun _ => standardNormal)) ≤
      ((Fintype.card ι : ℝ)+1) * x^(2*Fintype.card ι) := by
  classical
  let N := Fintype.card ι
  rw [gaussian_charpoly_second_moment_cardinality]
  calc
    (∑ k ∈ Finset.range (N+1),
      (((N.choose k * k.factorial : ℕ) : ℝ) * x^(2*(N-k)))) ≤
        ∑ _k ∈ Finset.range (N+1), x^(2*N) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          have hnat : N.choose k * k.factorial ≤ N^k := by
            rw [Nat.mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
            exact Nat.descFactorial_le_pow N k
          have hcoef : (((N.choose k * k.factorial : ℕ) : ℝ)) ≤ (N : ℝ)^k := by
            exact_mod_cast hnat
          have hpow : (N : ℝ)^k ≤ (x^2)^k :=
            pow_le_pow_left₀ (Nat.cast_nonneg N) hscale k
          have hnonneg : 0 ≤ x^(2*(N-k)) := pow_nonneg hx _
          have hmul := mul_le_mul_of_nonneg_right (hcoef.trans hpow) hnonneg
          calc
            _ ≤ (x^2)^k * x^(2*(N-k)) := hmul
            _ = (x^2)^N := by
              calc
                (x^2)^k * x^(2*(N-k)) =
                    (x^2)^k * (x^2)^(N-k) := by
                      rw [pow_mul]
                _ = (x^2)^N := by
                  rw [← pow_add]
                  congr 1
                  omega
            _ = x^(2*N) := by rw [pow_mul]
    _ = ((N : ℝ)+1) * x^(2*N) := by
      simp [nsmul_eq_mul, Nat.cast_add]

#print axioms gaussian_charpoly_second_moment_exterior_bound
end SpectralRadiusUpperTail
