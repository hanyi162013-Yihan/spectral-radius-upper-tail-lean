import SpectralRadiusUpperTail.SharpArrangementCode

namespace SpectralRadiusUpperTail

abbrev SharpDefectCode {L : ℕ} (s : Fin L → Bool) (g M : ℕ) :=
  Σ S : Fin (8*g+2), SharpArrangementCode s S.val (8*g) (2*L) M (8*g) (8*g+1)

/-- Explicit non-matching overhead, before simplifying to a power of length. -/
def defectCodeCost (L g : ℕ) :=
  (8*g+2) * (((8*g+1)*(max 1 L)^(8*g)) *
    ((L+1)^(8*g+1) * (max 1 (4*(8*g+1)))^(8*g+1))) *
    (pairRecordCost (2*L) (8*g) * pairRecordCost (L+1) (8*g+1))

lemma arrangement_size_factor_le (L S T : ℕ) (hST : S ≤ T) :
    (L+1)^S * (4*S)^S ≤ (L+1)^T * (max 1 (4*T))^T := by
  apply Nat.mul_le_mul
  · exact Nat.pow_le_pow_right (by omega) hST
  · exact (Nat.pow_le_pow_left ((Nat.mul_le_mul_left 4 hST).trans (le_max_right 1 (4*T))) S).trans
      (Nat.pow_le_pow_right (le_max_left 1 (4*T)) hST)

lemma sharpDefectCode_count_le {L : ℕ} (s : Fin L → Bool) (g M : ℕ) :
    Nat.card (SharpDefectCode s g M) ≤ M * defectCodeCost L g := by
  let D := (8*g+1)*(max 1 L)^(8*g)
  let T := (L+1)^(8*g+1) * (max 1 (4*(8*g+1)))^(8*g+1)
  let P := pairRecordCost (2*L) (8*g) * pairRecordCost (L+1) (8*g+1)
  have h := finite_sigma_count_le
    (fun S : Fin (8*g+2) => SharpArrangementCode s S.val (8*g) (2*L) M (8*g) (8*g+1))
    (D*T*(M*P)) (by
      intro S
      have hs := sharpArrangementCode_count_le s S.val (8*g) (2*L) M (8*g) (8*g+1)
      exact hs.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left D
        (arrangement_size_factor_le L S.val (8*g+1) (Nat.le_of_lt_succ S.isLt)))))
  have hfin : Nat.card (Fin (8*g+2)) = 8*g+2 := by simp
  rw [hfin] at h
  calc
    Nat.card (SharpDefectCode s g M) ≤ (8*g+2)*(D*T*(M*P)) := h
    _ = M * defectCodeCost L g := by unfold defectCodeCost D T P; ac_rfl

#print axioms SharpDefectCode
#print axioms defectCodeCost
#print axioms arrangement_size_factor_le
#print axioms sharpDefectCode_count_le
end SpectralRadiusUpperTail
