import SpectralRadiusUpperTail.GaussianStoppedRow

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators
variable {𝕂 : Type*} [RCLike 𝕂] [MeasurableSpace 𝕂] [BorelSpace 𝕂]
  [SecondCountableTopology 𝕂]

def terminalCoefficientMask (v : ℕ → 𝕂) (N n : ℕ) (i : Fin N) : 𝕂 :=
  if N-n ≤ i.val then v i.val else 0

lemma terminalCoefficientMask_energy (v : ℕ → 𝕂) (N n : ℕ)
    (hv : ∑ i : Fin N, ‖v i.val‖^2 ≤ 1) :
    ∑ i : Fin N, ‖terminalCoefficientMask v N n i‖^2 ≤ 1 := by
  apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) hv
  unfold terminalCoefficientMask
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using sq_nonneg ‖v i.val‖

/-- Every terminal history target is exactly a masked full-row linear form. -/
lemma gaussianTerminalTarget_eq_mask (v : ℕ → 𝕂) (N : ℕ) (t : 𝕂) (n : ℕ)
    (hn : n ≤ N) (x : Fin N → 𝕂 × 𝕂) :
    gaussianTerminalTarget v N t n x =
      t-∑ i : Fin N, terminalCoefficientMask v N n i*(x i).1 := by
  unfold gaussianTerminalTarget
  rw [terminalRevealedSum_of_le _ N n hn]
  congr 1
  dsimp only [Function.comp_def, revealedSum, pathSuffix]
  simp only [terminalCoefficientMask, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun (i : Fin n) _ => (⟨N-n+i.val, by omega⟩ : Fin N))
  · intro i _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro i _ k _ hik
    apply Fin.ext
    have hh := congrArg Fin.val hik
    dsimp at hh
    omega
  · intro i hi
    have hi' : N-n ≤ i.val := (Finset.mem_filter.mp hi).2
    refine ⟨⟨i.val-(N-n), by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    dsimp
    omega
  · intro i _
    rfl

#print axioms gaussianTerminalTarget_eq_mask
end SpectralRadiusUpperTail
