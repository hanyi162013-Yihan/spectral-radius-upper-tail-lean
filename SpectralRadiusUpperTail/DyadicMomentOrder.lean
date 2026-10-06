import Mathlib.Data.Nat.Log
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecificLimits.Normed

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

/-- A dyadic order growing as a small positive power of dimension. -/
def dyadicMomentOrder (d n : ℕ) : ℕ := 2^(Nat.log 2 n / d + 1)

lemma dyadicMomentOrder_pos (d n : ℕ) : 0 < dyadicMomentOrder d n := by
  unfold dyadicMomentOrder
  positivity

lemma dimension_lt_dyadicOrder_pow (d : ℕ) (hd : 0 < d) (n : ℕ) :
    n < (dyadicMomentOrder d n)^d := by
  have hh := Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  have he : Nat.log 2 n + 1 ≤ (Nat.log 2 n / d + 1)*d := by
    have hr := Nat.mod_lt (Nat.log 2 n) hd
    have hdiv := Nat.mod_add_div (Nat.log 2 n) d
    rw [Nat.add_mul,one_mul,Nat.mul_comm (Nat.log 2 n / d) d]
    omega
  exact hh.trans_le (by rw [dyadicMomentOrder, ← pow_mul]; exact Nat.pow_le_pow_right (by decide) he)

lemma dyadicOrder_pow_le_dimension (d n : ℕ) (hn : n ≠ 0) :
    (dyadicMomentOrder d n)^d ≤ 2^d*n := by
  rw [dyadicMomentOrder, ← pow_mul,Nat.add_mul,one_mul,pow_add]
  have hh : 2^((Nat.log 2 n / d)*d) ≤ n :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.div_mul_le_self _ _)).trans
      (Nat.pow_log_le_self 2 hn)
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_right (2^d) hh

lemma dyadicMomentOrder_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (dyadicMomentOrder d) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b^d)] with n hn
  have hh := dimension_lt_dyadicOrder_pow d hd n
  by_contra hb
  have hle : dyadicMomentOrder d n ≤ b := by omega
  have hp := Nat.pow_le_pow_left hle d
  omega

#print axioms dyadicMomentOrder
#print axioms dimension_lt_dyadicOrder_pow
#print axioms dyadicOrder_pow_le_dimension
#print axioms dyadicMomentOrder_tendsto
end SpectralRadiusUpperTail
