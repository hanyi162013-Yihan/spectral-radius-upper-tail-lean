import SpectralRadiusUpperTail.CharpolyPrincipalMinorEvaluation
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- The characteristic polynomial of a real matrix at a complex argument,
expanded over real principal minors. -/
theorem real_charpoly_complex_eval_eq_sum_principalMinors
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (z : ℂ) :
    (M.map Complex.ofRealHom).charpoly.eval z =
      ∑ s : Finset ι,
        ((-1 : ℂ)^s.card * z^(Fintype.card ι-s.card)) *
          (((M.submatrix (Subtype.val : s → ι)
            (Subtype.val : s → ι)).det : ℝ) : ℂ) := by
  classical
  let N := Fintype.card ι
  have hN : (M.map Complex.ofRealHom).charpoly.natDegree = N :=
    (M.map Complex.ofRealHom).charpoly_natDegree_eq_dim
  rw [Polynomial.eval_eq_sum_range, hN]
  rw [← Finset.sum_range_reflect
    (fun i => (M.map Complex.ofRealHom).charpoly.coeff i * z^i) (N+1)]
  simp only [Nat.add_sub_cancel_right]
  let f : Finset ι → ℂ := fun s =>
    ((-1 : ℂ)^s.card * z^(N-s.card)) *
      (((M.submatrix (Subtype.val : s → ι)
        (Subtype.val : s → ι)).det : ℝ) : ℂ)
  calc
    (∑ k ∈ Finset.range (N+1),
      (M.map Complex.ofRealHom).charpoly.coeff (N-k) * z^(N-k)) =
        ∑ k ∈ Finset.range (N+1),
          ∑ s ∈ (Finset.univ : Finset ι).powersetCard k, f s := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [Matrix.charpoly_coeff_eq_sum_minors _ k hkN,
        Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s hs
      have hcard : s.card = k := (Finset.mem_powersetCard.mp hs).2
      dsimp [f]
      rw [hcard]
      rw [Matrix.submatrix_map]
      have hdet :
          ((M.submatrix (Subtype.val : s → ι)
            (Subtype.val : s → ι)).map Complex.ofRealHom).det =
          (((M.submatrix (Subtype.val : s → ι)
            (Subtype.val : s → ι)).det : ℝ) : ℂ) := by
        change (Complex.ofRealHom.mapMatrix
          (M.submatrix (Subtype.val : s → ι)
            (Subtype.val : s → ι))).det = _
        exact (RingHom.map_det Complex.ofRealHom _).symm
      rw [hdet]
      ring
    _ = ∑ s : Finset ι, f s := by
      calc
        _ = ∑ k ∈ Finset.range (N+1),
          ∑ s : Finset ι, if s.card = k then f s else 0 := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.powersetCard_eq_filter, Finset.powerset_univ,
              Finset.sum_filter]
        _ = ∑ s : Finset ι,
          ∑ k ∈ Finset.range (N+1),
            if s.card = k then f s else 0 := Finset.sum_comm
        _ = ∑ s : Finset ι, f s := by
          apply Finset.sum_congr rfl
          intro s hs
          have hle : s.card ≤ N := Finset.card_le_univ s
          simp [Finset.mem_range, Nat.lt_succ_of_le hle]
    _ = _ := rfl

#print axioms real_charpoly_complex_eval_eq_sum_principalMinors
end SpectralRadiusUpperTail
