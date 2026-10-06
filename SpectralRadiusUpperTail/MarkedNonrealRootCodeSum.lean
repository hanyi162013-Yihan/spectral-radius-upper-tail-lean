import SpectralRadiusUpperTail.MarkedNonrealCodeCoverage
import SpectralRadiusUpperTail.MarkedNonrealCodeWeight

namespace SpectralRadiusUpperTail
open Classical
open scoped ENNReal

/-- Summing realized marked-pair classes counts each upper-half-plane
eigenvalue exactly once, with arbitrary nonnegative weights. -/
theorem markedNonreal_realized_code_weight_sum
    (m : ℕ) (hm : 0 < m)
    (A : Matrix (RealSchurMixedCoord (markedNonrealBlockSizes m))
      (RealSchurMixedCoord (markedNonrealBlockSizes m)) ℝ)
    (hA : A.charpoly.Separable) (g : ℂ → ℝ≥0∞) :
    (∑ code : Fin 2 → Fin (Fintype.card (RealSchurMixedCoord (markedNonrealBlockSizes m))) → Bool,
      if A ∈ realSchurMixedCodeClass (markedNonrealBlockSizes m) code then
        markedNonrealCodeWeight m A code g else 0) =
      ∑ i, if 0 < (realSchurMixedCanonicalSpectrum (markedNonrealBlockSizes m) A i).im then
        g (realSchurMixedCanonicalSpectrum (markedNonrealBlockSizes m) A i) else 0 := by
  classical
  let s := markedNonrealBlockSizes m
  let z := realSchurMixedCanonicalSpectrum s A
  have hdistrib : (∑ code : Fin 2 → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool,
      if A ∈ realSchurMixedCodeClass s code then markedNonrealCodeWeight m A code g else 0) =
      ∑ code : Fin 2 → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool,
        ∑ i, if A ∈ realSchurMixedCodeClass s code ∧ code 0 i=true ∧ 0 < (z i).im then
          g (z i) else 0 := by
    apply Finset.sum_congr rfl
    intro code hc
    by_cases h : A ∈ realSchurMixedCodeClass s code <;>
      simp [markedNonrealCodeWeight,h,s,z]
  rw [hdistrib,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  change (∑ code, if A ∈ realSchurMixedCodeClass s code ∧ code 0 i=true ∧ 0 < (z i).im then
    g (z i) else 0) = if 0 < (z i).im then g (z i) else 0
  by_cases hpos : 0 < (z i).im
  · obtain ⟨code,hcode,hci⟩ := markedNonreal_realized_code_exists m hm A hA i (ne_of_gt hpos)
    change A ∈ realSchurMixedCodeClass s code at hcode
    rw [Finset.sum_eq_single code]
    · simp [hcode,hci,hpos]
    · intro other ho hne
      by_cases h : A ∈ realSchurMixedCodeClass s other ∧ other 0 i=true ∧ 0 < (z i).im
      · have heq := markedNonreal_realized_code_unique m hm A hA other code h.1 hcode i
          (ne_of_gt hpos) h.2.1 hci
        exact False.elim (hne heq)
      · exact if_neg h
    · simp
  · simp [hpos]

theorem markedNonreal_realized_code_count_le
    (m : ℕ) (hm : 0 < m)
    (A : Matrix (RealSchurMixedCoord (markedNonrealBlockSizes m))
      (RealSchurMixedCoord (markedNonrealBlockSizes m)) ℝ)
    (hA : A.charpoly.Separable) :
    (∑ code : Fin 2 → Fin (Fintype.card (RealSchurMixedCoord (markedNonrealBlockSizes m))) → Bool,
      if A ∈ realSchurMixedCodeClass (markedNonrealBlockSizes m) code then
        markedNonrealCodeWeight m A code (fun _ => 1) else 0) ≤ (m+2 : ℕ) := by
  classical
  rw [markedNonreal_realized_code_weight_sum m hm A hA (fun _ => 1)]
  calc
    _ ≤ ∑ _i : Fin (Fintype.card (RealSchurMixedCoord (markedNonrealBlockSizes m))), (1 : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs
      · exact le_rfl
      · exact zero_le
    _ = _ := by simp [markedNonrealCoord_card,add_comm]

#print axioms markedNonreal_realized_code_weight_sum
#print axioms markedNonreal_realized_code_count_le
end SpectralRadiusUpperTail
