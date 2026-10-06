import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped BigOperators

lemma sum_nonneg_cubes_le_cube_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) : (∑ i ∈ s, (f i)^3) ≤ (∑ i ∈ s, f i)^3 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hs := Finset.sum_nonneg hfs
    have hi := ih hfs
    simp only [Finset.sum_insert ha]
    nlinarith [mul_nonneg (sq_nonneg (f a)) hs, mul_nonneg hfa (sq_nonneg (∑ i ∈ s, f i))]

/-- The triple-factorial series in the Schur path count grows at most like
exp(3a) when its numerator parameter is a^3. Only nonnegative terms are used. -/
lemma schur_factorial_sum_le_exp (a : ℝ) (ha : 0 ≤ a) (L : ℕ) :
    (∑ l ∈ Finset.range L, (a^3)^l/(l.factorial : ℝ)^3) ≤ Real.exp (3*a) := by
  have he (l : ℕ) : (a^3)^l/(l.factorial : ℝ)^3 = (a^l/(l.factorial : ℝ))^3 := by
    rw [div_pow, ← pow_mul, ← pow_mul, Nat.mul_comm 3 l]
  simp_rw [he]
  have hs := sum_nonneg_cubes_le_cube_sum (Finset.range L)
    (fun l => a^l/(l.factorial : ℝ)) (fun l _ => by positivity)
  have hb := pow_le_pow_left₀ (Finset.sum_nonneg (fun l _ => by positivity))
    (Real.sum_le_exp_of_nonneg ha L) 3
  apply hs.trans (hb.trans_eq ?_)
  rw [← Real.exp_nat_mul]
  norm_num

/-- The concrete k^(2/3) Schur combinatorial envelope, for every finite path
length cutoff. The parameter C need only be nonnegative. -/
lemma schur_factorial_sum_cuberoot (C : ℝ) (hC : 0 ≤ C) (k L : ℕ) :
    (∑ l ∈ Finset.range L, (C*(k : ℝ)^2)^l/(l.factorial : ℝ)^3) ≤
      Real.exp (3*(C*(k : ℝ)^2)^((1 : ℝ)/3)) := by
  let a := (C*(k : ℝ)^2)^((1 : ℝ)/3)
  have ha : 0 ≤ a := Real.rpow_nonneg (by positivity) _
  have he : a^3 = C*(k : ℝ)^2 := by
    dsimp [a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  simpa only [he] using schur_factorial_sum_le_exp a ha L

#print axioms schur_factorial_sum_le_exp
#print axioms schur_factorial_sum_cuberoot
end SpectralRadiusUpperTail
