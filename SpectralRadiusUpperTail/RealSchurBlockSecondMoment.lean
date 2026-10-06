import SpectralRadiusUpperTail.RealSchurPaddedPowerGaussianSum

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

/-- Exact path Parseval identity for one block of the padded Gaussian Schur
product model. Paths may share vertices and bridge entries. -/
theorem real_schur_block_path_second_moment {N : ℕ}
    (n k : ℕ) (hn : 0 < n) (η ρ : ℝ) (hη : 0 < η)
    (B : Fin N → RealSchurBlockData)
    (hB : ∀ i, realSchurDataAdmissible (B i))
    (hmod : ∀ i, realSchurDataRadius (B i) ≤ ρ)
    (i j : Fin N) :
    Integrable (fun z => ‖realSchurBlockPowerPathSum n k B i j z‖^2)
      (realSchurGlobalLaw n B) ∧
    (∫ z, ‖realSchurBlockPowerPathSum n k B i j z‖^2
      ∂realSchurGlobalLaw n B) =
      ∑ p : SchurFixedStartFiniteFamily N k i,
        if anyPathLast (schurFixedStartFinitePath p) = j then
          ∫ z, ‖realSchurGlobalWaitingSum n k B
            (schurFixedStartFinitePath p) z‖^2 ∂realSchurGlobalLaw n B
        else 0 := by
  haveI (u : Fin N) := realSchurDataLaw_probability
    (n : ℝ) (Nat.cast_pos.mpr hn) (B u) (hB u)
  haveI : IsProbabilityMeasure (realSchurGlobalLaw n B) := by
    dsimp [realSchurGlobalLaw]
    infer_instance
  let F : SchurFixedStartFiniteFamily N k i →
      ((Fin N → ℝ) × (SchurEntryIndex N 2 → ℝ)) →
      Matrix (Fin 2) (Fin 2) ℝ :=
    fun p z => if anyPathLast (schurFixedStartFinitePath p) = j then
      realSchurGlobalWaitingSum n k B (schurFixedStartFinitePath p) z else 0
  have hF (p : SchurFixedStartFiniteFamily N k i) (a b : Fin 2) :
      Measurable (fun z => F p z a b) := by
    dsimp [F]
    split_ifs
    · exact realSchurGlobalWaitingSum_entry_measurable n k hn B hB _ a b
    · exact measurable_const
  have hi (p : SchurFixedStartFiniteFamily N k i) :
      Integrable (fun z => ‖F p z‖^2) (realSchurGlobalLaw n B) := by
    dsimp [F]
    split_ifs
    · exact (real_schur_global_waiting_second_moment n k hn η ρ hη B hB hmod
        (schurFixedStartFinitePath p)
        (schurFixedStartFinitePath_length_le p)).1
    · exact integrable_const _
  have ho (p q : SchurFixedStartFiniteFamily N k i)
      (hpq : p ≠ q) (a b : Fin 2) :
      (∫ z, F p z a b * F q z a b ∂realSchurGlobalLaw n B) = 0 := by
    dsimp [F]
    split_ifs with hp hq
    · exact real_schur_global_waiting_cross_zero n k hn η ρ hη B hB hmod
        (schurFixedStartFinitePath p) (schurFixedStartFinitePath q)
        (schurFixedStartFinitePath_length_le p)
        (schurFixedStartFinitePath_length_le q)
        (hp.trans hq.symm)
        (fun h => hpq (schurFixedStartFinitePath_injective h)) a b
    · simp
    · simp
    · simp
  have hh := matrix_orthogonal_second_moment_of_squares
    (realSchurGlobalLaw n B) F hF hi ho
  constructor
  · change Integrable (fun z => ‖∑ p, F p z‖^2)
      (realSchurGlobalLaw n B)
    exact hh.1
  · change (∫ z, ‖∑ p, F p z‖^2 ∂realSchurGlobalLaw n B) = _
    rw [hh.2]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : anyPathLast (schurFixedStartFinitePath p) = j
    · simp [F, hp]
    · simp [F, hp]

#print axioms real_schur_block_path_second_moment
end SpectralRadiusUpperTail
