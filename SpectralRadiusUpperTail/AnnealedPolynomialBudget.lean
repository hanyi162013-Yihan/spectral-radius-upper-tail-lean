import SpectralRadiusUpperTail.PolynomialExponentialBudget

namespace SpectralRadiusUpperTail
open Filter
open scoped Topology

lemma eventually_annealed_polynomial_budget (M : ℕ) (r : ℝ) (hr : 0 < r) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ B : ℝ,
      ((M+1 : ℕ) : ℝ)*((n : ℝ)+1)^M*r^(n-M)*Real.exp ((n : ℝ)*B) ≤
        Real.exp ((n : ℝ)*(Real.log r+B+ε)) := by
  let C := ((M+1 : ℕ) : ℝ)/(r^M)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  filter_upwards [eventually_polynomial_prefactor_le_exp C hC M ε hε, eventually_ge_atTop M]
    with n hn hMn B
  have hp : r^n = r^M*r^(n-M) := by rw [← pow_add, Nat.add_sub_of_le hMn]
  have he : ((M+1 : ℕ) : ℝ)*((n : ℝ)+1)^M*r^(n-M) = C*((n : ℝ)+1)^M*r^n := by
    rw [hp]
    dsimp [C]
    field_simp
  have hexp : r^n = Real.exp ((n : ℝ)*Real.log r) := by rw [Real.exp_nat_mul, Real.exp_log hr]
  rw [he, hexp]
  calc
    _ ≤ Real.exp ((n : ℝ)*ε)*Real.exp ((n : ℝ)*Real.log r)*Real.exp ((n : ℝ)*B) := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

lemma exists_large_target_cutoff (R D ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 ≤ t → t ≤ R^2 → (t/K^2)*D ≤ ε := by
  let K := R^2*D/ε+1
  have hK : 1 ≤ K := by
    dsimp [K]
    have hh : 0 ≤ R^2*D/ε := by positivity
    linarith
  have he : ε*(R^2*D/ε) = R^2*D := mul_div_cancel₀ _ hε.ne'
  refine ⟨K, by linarith, ?_⟩
  intro t ht htR
  have hb : R^2*D ≤ ε*K^2 := by
    have hh : K ≤ K^2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hh hε.le
    dsimp [K] at hm
    nlinarith
  have hm := mul_le_mul_of_nonneg_right htR hD
  have hK2 : 0 < K^2 := sq_pos_of_pos (by linarith)
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hK2).mpr (hm.trans hb)

#print axioms eventually_annealed_polynomial_budget
#print axioms exists_large_target_cutoff
end SpectralRadiusUpperTail
