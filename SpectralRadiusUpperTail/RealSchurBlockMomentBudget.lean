import SpectralRadiusUpperTail.RealSchurBlockSecondMoment
import SpectralRadiusUpperTail.SchurFixedStartMomentBudget
import SpectralRadiusUpperTail.FiniteMaskedSumBound

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

/-- A complete second-moment bound for one block of a positive power of
the padded conditional Schur product model. -/
theorem real_schur_block_power_second_moment_bound {N : ℕ}
    (n k : ℕ) (hn : 0 < n) (hN : N ≤ n)
    (η ρ : ℝ) (hη : 0 < η) (hR : 0 < ρ+η)
    (B : Fin N → RealSchurBlockData)
    (hB : ∀ i, realSchurDataAdmissible (B i))
    (hmod : ∀ i, realSchurDataRadius (B i) ≤ ρ)
    (i j : Fin N) :
    (∫ z, ‖realSchurBlockPowerPathSum n k B i j z‖^2
      ∂realSchurGlobalLaw n B) ≤
      (2+2/((n : ℝ)*η^2))*(n : ℝ)*(ρ+η)^(2*k)*
        Real.exp (3*((4*(2+2/((n : ℝ)*η^2))/(ρ+η)^2)*
          (k : ℝ)^2)^((1 : ℝ)/3)) := by
  classical
  let C : ℝ := 2+2/((n : ℝ)*η^2)
  let R : ℝ := ρ+η
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpos := (real_schur_block_path_second_moment
    n k hn η ρ hη B hB hmod i j).2
  let budget : ℕ → ℝ := fun l =>
    C^(l+1)*(1/(n : ℝ))^l*(k.choose l : ℝ)^2*R^(2*(k-l))
  have hbudget (l : ℕ) : 0 ≤ budget l := by dsimp [budget]; positivity
  have hpath (p : SchurFixedStartFiniteFamily N k i) :
      (∫ z, ‖realSchurGlobalWaitingSum n k B
        (schurFixedStartFinitePath p) z‖^2 ∂realSchurGlobalLaw n B) ≤
      budget p.1.val := by
    have hp := (real_schur_global_waiting_second_moment
      n k hn η ρ hη B hB hmod (schurFixedStartFinitePath p)
      (schurFixedStartFinitePath_length_le p)).2
    calc
      _ ≤ (k.choose p.1.val : ℝ)^2 *
          ((1/(n : ℝ))^p.1.val * C^(p.1.val+1) *
            R^(2*(k-p.1.val))) := by
        simpa only [C, R, schurFixedStartFinitePath] using hp
      _ = budget p.1.val := by dsimp [budget]; ring
  calc
    (∫ z, ‖realSchurBlockPowerPathSum n k B i j z‖^2
      ∂realSchurGlobalLaw n B) =
      ∑ p : SchurFixedStartFiniteFamily N k i,
        if anyPathLast (schurFixedStartFinitePath p) = j then
          ∫ z, ‖realSchurGlobalWaitingSum n k B
            (schurFixedStartFinitePath p) z‖^2 ∂realSchurGlobalLaw n B
        else 0 := hpos
    _ = ∑ l : Fin (k+1),
        ∑ p : {p : IncreasingBlockPath N l.val // p.val 0 = i},
          if anyPathLast (⟨l.val,p.val⟩ : AnyIncreasingPath N) = j then
            ∫ z, ‖realSchurGlobalWaitingSum n k B
              ⟨l.val,p.val⟩ z‖^2 ∂realSchurGlobalLaw n B
          else 0 := by
        rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro l hl
        apply Finset.sum_congr
        · ext p
          simp
        · intro p hp
          rfl
    _ ≤ ∑ l : Fin (k+1),
        (Fintype.card {p : IncreasingBlockPath N l.val // p.val 0 = i} : ℝ)*
          budget l.val := by
      apply Finset.sum_le_sum
      intro l hl
      exact finite_masked_sum_le_card_mul
        (fun p : {p : IncreasingBlockPath N l.val // p.val 0 = i} =>
          anyPathLast (⟨l.val,p.val⟩ : AnyIncreasingPath N) = j)
        (fun p => ∫ z, ‖realSchurGlobalWaitingSum n k B
          ⟨l.val,p.val⟩ z‖^2 ∂realSchurGlobalLaw n B)
        (budget l.val) (hbudget l.val)
        (fun p => hpath ⟨l,p⟩)
    _ ≤ C*(n : ℝ)*R^(2*k)*
        Real.exp (3*((4*C/R^2)*(k : ℝ)^2)^((1 : ℝ)/3)) := by
      have hs :
          (∑ l : Fin (k+1),
            (Fintype.card {p : IncreasingBlockPath N l.val // p.val 0 = i} : ℝ)*
              budget l.val) =
          (∑ l ∈ Finset.range (k+1),
            (Fintype.card {p : IncreasingBlockPath N l // p.val 0 = i} : ℝ)*
              C^(l+1)*(1/(n : ℝ))^l*(k.choose l : ℝ)^2*
                R^(2*(k-l))) := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro l hl
        dsimp [budget]
        ring
      rw [hs]
      exact schur_fixed_start_moment_budget n k hn hN i C R hC hR
    _ = _ := rfl

#print axioms real_schur_block_power_second_moment_bound
end SpectralRadiusUpperTail
