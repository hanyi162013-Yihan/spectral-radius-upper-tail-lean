import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

lemma half_gamma_square_upper (n : ℕ) (hn : 4 ≤ n) :
    (Real.Gamma ((n : ℝ)/2+1))^2 ≤
      ((n : ℝ)/2+1/2)*(n.factorial : ℝ)*(2 : ℝ)^(-(n : ℝ))*Real.sqrt Real.pi := by
  have hnreal : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hm := Real.Gamma_strictMonoOn_Ici.monotoneOn
    (show (n : ℝ)/2+1 ∈ Set.Ici (2 : ℝ) by exact (show (2 : ℝ) ≤ (n : ℝ)/2+1 by linarith))
    (show (n : ℝ)/2+1/2+1 ∈ Set.Ici (2 : ℝ) by exact (show (2 : ℝ) ≤ (n : ℝ)/2+1/2+1 by linarith))
    (show (n : ℝ)/2+1 ≤ (n : ℝ)/2+1/2+1 by linarith)
  rw [Real.Gamma_add_one (by linarith : (n : ℝ)/2+1/2 ≠ 0)] at hm
  have hp := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (n : ℝ)/2+1)
  have hmul := mul_le_mul_of_nonneg_right hm hp.le
  have hd := Real.Gamma_mul_Gamma_add_half ((n : ℝ)/2+1/2)
  have he1 : (n : ℝ)/2+1/2+1/2 = (n : ℝ)/2+1 := by ring
  have he2 : 2*((n : ℝ)/2+1/2) = (n : ℝ)+1 := by ring
  have he3 : 1-2*((n : ℝ)/2+1/2) = -(n : ℝ) := by ring
  rw [he1,he3,he2,Real.Gamma_nat_eq_factorial] at hd
  calc
    _ ≤ (((n : ℝ)/2+1/2)*Real.Gamma ((n : ℝ)/2+1/2))*Real.Gamma ((n : ℝ)/2+1) := by
      simpa only [pow_two] using hmul
    _ = _ := by rw [mul_assoc,hd]; ring

lemma half_gamma_log_upper (n : ℕ) (hn : 4 ≤ n) :
    2*Real.log (Real.Gamma ((n : ℝ)/2+1)) ≤
      Real.log (n.factorial : ℝ)-(n : ℝ)*Real.log 2+
        Real.log (Real.sqrt Real.pi)+Real.log ((n : ℝ)/2+1/2) := by
  have hG := Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (n : ℝ)/2+1)
  have hh := Real.log_le_log (sq_pos_of_pos hG) (half_gamma_square_upper n hn)
  rw [Real.log_pow,Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hh
  nlinarith

#print axioms half_gamma_square_upper
#print axioms half_gamma_log_upper
end SpectralRadiusUpperTail
