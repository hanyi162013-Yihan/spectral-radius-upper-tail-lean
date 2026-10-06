import SpectralRadiusUpperTail.RealSchurGlobalOrthogonality
import SpectralRadiusUpperTail.SchurFinitePathFamily

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

/-- Sum all paths ending at one terminal block in the common global model. -/
noncomputable def realSchurTerminalSum {N : ℕ} (n k : ℕ)
    (B : Fin N → RealSchurBlockData) (terminal : Fin N)
    (z : (Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) : Matrix (Fin 2) (Fin 2) ℝ :=
  ∑ p : SchurFinitePathFamily N k,
    if anyPathLast (schurFinitePath p) = terminal then
      realSchurGlobalWaitingSum n k B (schurFinitePath p) z else 0

/-- Within each terminal block, distinct strict paths are orthogonal. -/
theorem real_schur_terminal_second_moment {N : ℕ} (n k : ℕ) (hn : 0 < n)
    (η ρ : ℝ) (hη : 0 < η) (B : Fin N → RealSchurBlockData)
    (hB : ∀ i, realSchurDataAdmissible (B i))
    (hmod : ∀ i, realSchurDataRadius (B i) ≤ ρ) (terminal : Fin N) :
    Integrable (fun z => ‖realSchurTerminalSum n k B terminal z‖^2)
      (realSchurGlobalLaw n B) ∧
    (∫ z, ‖realSchurTerminalSum n k B terminal z‖^2 ∂realSchurGlobalLaw n B) =
      ∑ p : SchurFinitePathFamily N k,
        if anyPathLast (schurFinitePath p) = terminal then
          ∫ z, ‖realSchurGlobalWaitingSum n k B (schurFinitePath p) z‖^2
            ∂realSchurGlobalLaw n B else 0 := by
  haveI (i : Fin N) := realSchurDataLaw_probability (n : ℝ) (Nat.cast_pos.mpr hn) (B i) (hB i)
  haveI : IsProbabilityMeasure (realSchurGlobalLaw n B) := by
    dsimp [realSchurGlobalLaw]
    infer_instance
  let F : SchurFinitePathFamily N k →
      ((Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) → Matrix (Fin 2) (Fin 2) ℝ :=
    fun p z => if anyPathLast (schurFinitePath p) = terminal then
      realSchurGlobalWaitingSum n k B (schurFinitePath p) z else 0
  have hF (p : SchurFinitePathFamily N k) (a b : Fin 2) :
      Measurable (fun z => F p z a b) := by
    dsimp [F]
    split_ifs
    · exact realSchurGlobalWaitingSum_entry_measurable n k hn B hB _ a b
    · exact measurable_const
  have hi (p : SchurFinitePathFamily N k) :
      Integrable (fun z => ‖F p z‖^2) (realSchurGlobalLaw n B) := by
    dsimp [F]
    split_ifs
    · exact (real_schur_global_waiting_second_moment n k hn η ρ hη B hB hmod
        (schurFinitePath p) (schurFinitePath_length_le p)).1
    · exact integrable_const _
  have ho (p q : SchurFinitePathFamily N k) (hpq : p ≠ q) (a b : Fin 2) :
      (∫ z, F p z a b * F q z a b ∂realSchurGlobalLaw n B) = 0 := by
    dsimp [F]
    split_ifs with hp hq
    · exact real_schur_global_waiting_cross_zero n k hn η ρ hη B hB hmod
        (schurFinitePath p) (schurFinitePath q)
        (schurFinitePath_length_le p) (schurFinitePath_length_le q)
        (hp.trans hq.symm) (fun h => hpq (schurFinitePath_injective h)) a b
    · simp
    · simp
    · simp
  have hh := matrix_orthogonal_second_moment_of_squares (realSchurGlobalLaw n B)
    F hF hi ho
  constructor
  · change Integrable (fun z => ‖∑ p, F p z‖^2) (realSchurGlobalLaw n B)
    exact hh.1
  · change (∫ z, ‖∑ p, F p z‖^2 ∂realSchurGlobalLaw n B) = _
    rw [hh.2]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : anyPathLast (schurFinitePath p) = terminal
    · simp [F, hp]
    · simp [F, hp]

#print axioms real_schur_terminal_second_moment
end SpectralRadiusUpperTail
