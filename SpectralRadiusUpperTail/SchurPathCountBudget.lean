import SpectralRadiusUpperTail.SchurSeriesBound
import Mathlib.Data.Nat.Choose.Bounds

namespace SpectralRadiusUpperTail
open scoped BigOperators

lemma schur_path_binomial_budget (n k l : ℕ) (hn : 0 < n) (D : ℝ) (hD : 0 ≤ D) :
    (n.choose (l+1) : ℝ)*(D/n)^l*(k.choose l : ℝ)^2 ≤
      (n : ℝ)*(D*(k : ℝ)^2)^l/(l.factorial : ℝ)^3 := by
  have hf : (0 : ℝ) < l.factorial := by positivity
  have hnf : (l.factorial : ℝ) ≤ (l+1).factorial := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ l)
  have hnc : (n.choose (l+1) : ℝ) ≤ (n : ℝ)^(l+1)/(l.factorial : ℝ) :=
    (Nat.choose_le_pow_div (l+1) n).trans
      (div_le_div_of_nonneg_left (by positivity) hf hnf)
  have hkc := Nat.choose_le_pow_div l k (α := ℝ)
  calc
    _ ≤ ((n : ℝ)^(l+1)/(l.factorial : ℝ))*(D/n)^l*
        ((k : ℝ)^l/(l.factorial : ℝ))^2 := by
      gcongr
    _ = _ := by
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      have hkpow : ((k : ℝ)^l)^2 = ((k : ℝ)^2)^l := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm l 2]
      simp only [div_pow, mul_pow, pow_succ, hkpow]
      field_simp
      <;> ring

/-- The full finite numerical path-count sum. This closes the combinatorial
summation once the probabilistic per-path estimate has been supplied. -/
theorem schur_path_count_sum_bound (n k L : ℕ) (hn : 0 < n) (D : ℝ) (hD : 0 ≤ D) :
    (∑ l ∈ Finset.range L, (n.choose (l+1) : ℝ)*(D/n)^l*(k.choose l : ℝ)^2) ≤
      (n : ℝ)*Real.exp (3*(D*(k : ℝ)^2)^((1 : ℝ)/3)) := by
  calc
    _ ≤ ∑ l ∈ Finset.range L, (n : ℝ)*(D*(k : ℝ)^2)^l/(l.factorial : ℝ)^3 :=
      Finset.sum_le_sum (fun l _ => schur_path_binomial_budget n k l hn D hD)
    _ = (n : ℝ)*(∑ l ∈ Finset.range L, (D*(k : ℝ)^2)^l/(l.factorial : ℝ)^3) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (schur_factorial_sum_cuberoot D hD k L) (Nat.cast_nonneg n)

#print axioms schur_path_binomial_budget
#print axioms schur_path_count_sum_bound
end SpectralRadiusUpperTail
