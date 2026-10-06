import SpectralRadiusUpperTail.RealSchurTerminalAssembly
import SpectralRadiusUpperTail.SchurFiniteFamilyDimensionBudget

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

noncomputable def realSchurTerminalEnergy {N : ℕ} (n k : ℕ)
    (B : Fin N → RealSchurBlockData)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) : ℝ :=
  ∑ terminal : Fin N, ‖realSchurTerminalSum n k B terminal z‖^2

/-- The entire finite Schur path model has a subexponential moment loss.
This theorem concerns the explicit common Gaussian array and block-gap laws;
it does not identify them with the conditional law of a real Ginibre matrix. -/
theorem real_schur_terminal_energy_bound (N n k : ℕ) (hN : N ≤ n) (hn : 0 < n)
    (η ρ : ℝ) (hη : 0 < η) (hR : 0 < ρ+η)
    (B : Fin N → RealSchurBlockData)
    (hB : ∀ i, realSchurDataAdmissible (B i))
    (hmod : ∀ i, realSchurDataRadius (B i) ≤ ρ) :
    Integrable (realSchurTerminalEnergy n k B) (realSchurGlobalLaw n B) ∧
    (∫ z, realSchurTerminalEnergy n k B z ∂realSchurGlobalLaw n B) ≤
      (2+2/((n : ℝ)*η^2))*(n : ℝ)*(ρ+η)^(2*k)*
        Real.exp (3*((4*(2+2/((n : ℝ)*η^2))/(ρ+η)^2)*(k : ℝ)^2)^((1 : ℝ)/3)) := by
  let C : ℝ := 2+2/((n : ℝ)*η^2)
  let R : ℝ := ρ+η
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hR' : 0 < R := hR
  have ht (terminal : Fin N) :=
    real_schur_terminal_second_moment n k hn η ρ hη B hB hmod terminal
  have hp (p : SchurFinitePathFamily N k) :=
    real_schur_global_waiting_second_moment n k hn η ρ hη B hB hmod
      (schurFinitePath p) (schurFinitePath_length_le p)
  have hcollapse (p : SchurFinitePathFamily N k) :
      (∑ terminal : Fin N,
        if anyPathLast (schurFinitePath p) = terminal then
          ∫ z, ‖realSchurGlobalWaitingSum n k B (schurFinitePath p) z‖^2
            ∂realSchurGlobalLaw n B else 0) =
      ∫ z, ‖realSchurGlobalWaitingSum n k B (schurFinitePath p) z‖^2
        ∂realSchurGlobalLaw n B := by
    rw [Finset.sum_eq_single (anyPathLast (schurFinitePath p))]
    · simp
    · intro terminal _ hne
      simp [Ne.symm hne]
    · simp
  have heq : (∫ z, realSchurTerminalEnergy n k B z ∂realSchurGlobalLaw n B) =
      ∑ p : SchurFinitePathFamily N k,
        ∫ z, ‖realSchurGlobalWaitingSum n k B (schurFinitePath p) z‖^2
          ∂realSchurGlobalLaw n B := by
    unfold realSchurTerminalEnergy
    rw [integral_finsetSum _ (fun terminal _ => (ht terminal).1)]
    simp_rw [(ht _).2]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    exact hcollapse p
  have hscale (l : ℕ) : (1/(n : ℝ))^l ≤ (4/(n : ℝ))^l := by
    apply pow_le_pow_left₀ (by positivity)
    · have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      apply (div_le_div_iff₀ hnR hnR).mpr
      nlinarith
  have hpath (p : SchurFinitePathFamily N k) :
      (∫ z, ‖realSchurGlobalWaitingSum n k B (schurFinitePath p) z‖^2
          ∂realSchurGlobalLaw n B) ≤
      (k.choose p.1.val : ℝ)^2 *
        (C^(p.1.val+1)*(4/(n : ℝ))^p.1.val*R^(2*(k-p.1.val))) := by
    have hmult : 0 ≤ (k.choose p.1.val : ℝ)^2*C^(p.1.val+1)*R^(2*(k-p.1.val)) := by
      positivity
    calc
      _ ≤ (k.choose p.1.val : ℝ)^2 *
        ((1/(n : ℝ))^p.1.val*C^(p.1.val+1)*R^(2*(k-p.1.val))) := (hp p).2
      _ = ((k.choose p.1.val : ℝ)^2*C^(p.1.val+1)*R^(2*(k-p.1.val))) *
        (1/(n : ℝ))^p.1.val := by ring
      _ ≤ ((k.choose p.1.val : ℝ)^2*C^(p.1.val+1)*R^(2*(k-p.1.val))) *
        (4/(n : ℝ))^p.1.val := mul_le_mul_of_nonneg_left (hscale _) hmult
      _ = _ := by ring
  constructor
  · unfold realSchurTerminalEnergy
    exact integrable_finsetSum _ (fun terminal _ => (ht terminal).1)
  · rw [heq]
    calc
      _ ≤ ∑ p : SchurFinitePathFamily N k,
          (k.choose p.1.val : ℝ)^2 *
            (C^(p.1.val+1)*(4/(n : ℝ))^p.1.val*R^(2*(k-p.1.val))) :=
        Finset.sum_le_sum (fun p _ => hpath p)
      _ ≤ C*(n : ℝ)*R^(2*k)*
          Real.exp (3*((4*C/R^2)*(k : ℝ)^2)^((1 : ℝ)/3)) :=
        schur_finite_family_dimension_budget N n k hN hn C R hC hR'
      _ = _ := rfl

#print axioms real_schur_terminal_energy_bound
end SpectralRadiusUpperTail
