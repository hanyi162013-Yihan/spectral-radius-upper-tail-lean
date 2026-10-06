import SpectralRadiusUpperTail.RealSchurFlattenedPowerEnergy

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Frobenius
open Classical

theorem realSchurDataPower_continuous (B : RealSchurBlockData) (k : ℕ) :
    Continuous (realSchurDataPower B k) := by
  cases B with
  | real x => exact continuous_const
  | pair x y =>
    have hh : Continuous (fun g => realSchurBlock x (schurGapUpper y g) (schurGapLower y g)) := by
      apply continuous_pi
      intro a
      apply continuous_pi
      intro b
      fin_cases a <;> fin_cases b <;>
        simp only [realSchurBlock,schurGapUpper,schurGapLower] <;> fun_prop
    exact hh.pow k

theorem realSchurPaddedMatrix_continuous {m : ℕ} (n : ℕ) (B : Fin m → RealSchurBlockData) :
    Continuous (realSchurPaddedMatrix n B) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold realSchurPaddedMatrix
  simp only [Matrix.of_apply]
  split_ifs
  · exact (realSchurDataPower_continuous (B i) 1).comp
      ((continuous_apply i).comp continuous_fst)
  · unfold realSchurPaddedBridge
    apply Continuous.mul
    · apply Continuous.mul
      · exact (realSchurDataPower_continuous (B i) 0).comp
          ((continuous_apply i).comp continuous_fst)
      · have hh : Continuous (fun z : (Fin m → ℝ) × (SchurEntryIndex m 2 → ℝ) =>
            Matrix.of (fun a b : Fin 2 => z.2 ((i,j),(a,b)))) := by
          apply continuous_pi
          intro a
          apply continuous_pi
          intro b
          exact (continuous_apply ((i,j),(a,b))).comp continuous_snd
        exact hh.const_smul (1/Real.sqrt n)
    · exact (realSchurDataPower_continuous (B j) 0).comp
        ((continuous_apply j).comp continuous_fst)
  · exact continuous_const

theorem realSchurFlattenedPowerEnergy_continuous {m : ℕ}
    (n k : ℕ) (B : Fin m → RealSchurBlockData) :
    Continuous (fun z => ‖(flattenSchurBlocks (realSchurPaddedMatrix n B z))^k‖^2) := by
  have hf : Continuous (flattenSchurBlocks (N := m)) := by
    unfold flattenSchurBlocks
    fun_prop
  exact ((hf.comp (realSchurPaddedMatrix_continuous n B)).pow k).norm.pow 2

#print axioms realSchurDataPower_continuous
#print axioms realSchurPaddedMatrix_continuous
#print axioms realSchurFlattenedPowerEnergy_continuous
end SpectralRadiusUpperTail
