import SpectralRadiusUpperTail.RealMatrixConjugateRoots
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

noncomputable def realMatrixUpperNonrealExteriorCount {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) : ℕ := by
  classical
  exact ((A.map Complex.ofRealHom).charpoly.roots).countP
    (fun z : ℂ => 0 < z.im ∧ r < ‖z‖)

noncomputable def realMatrixLowerNonrealExteriorCount {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) : ℕ := by
  classical
  exact ((A.map Complex.ofRealHom).charpoly.roots).countP
    (fun z : ℂ => z.im < 0 ∧ r < ‖z‖)

private theorem multiset_nonreal_exterior_count_split
    (s : Multiset ℂ) (r : ℝ) :
    s.countP (fun z : ℂ => z.im ≠ 0 ∧ r < ‖z‖) =
      s.countP (fun z : ℂ => 0 < z.im ∧ r < ‖z‖) +
      s.countP (fun z : ℂ => z.im < 0 ∧ r < ‖z‖) := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
    simp only [Multiset.countP_cons, ih]
    by_cases hr : r < ‖z‖
    · rcases lt_trichotomy z.im 0 with hm | hm | hm
      · have hne : z.im ≠ 0 := by linarith
        have hp : ¬ 0 < z.im := by linarith
        simp [hr, hm, hne, hp]
        omega
      · simp [hm]
      · have hne : z.im ≠ 0 := by linarith
        have hl : ¬ z.im < 0 := by linarith
        simp [hr, hm, hne, hl]
        omega
    · simp [hr]

theorem realMatrixUpperLowerNonrealCount_equal {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) :
    realMatrixUpperNonrealExteriorCount A r =
      realMatrixLowerNonrealExteriorCount A r := by
  classical
  unfold realMatrixUpperNonrealExteriorCount
    realMatrixLowerNonrealExteriorCount
  let s := (A.map Complex.ofRealHom).charpoly.roots
  have hs : s.map (starRingEnd ℂ) = s :=
    realMatrix_charpoly_roots_conj A
  change s.countP (fun z : ℂ => 0 < z.im ∧ r < ‖z‖) =
    s.countP (fun z : ℂ => z.im < 0 ∧ r < ‖z‖)
  calc
    _ = (s.map (starRingEnd ℂ)).countP
        (fun z : ℂ => 0 < z.im ∧ r < ‖z‖) := by rw [hs]
    _ = _ := by
      rw [Multiset.countP_map, Multiset.countP_eq_card_filter]
      congr 1
      apply Multiset.filter_congr
      intro z _
      simp [Complex.conj_im]

/-- Nonreal characteristic roots of a real matrix occur in conjugate
pairs, with multiplicity. The exterior nonreal count is twice the
upper-half-plane count. -/
theorem realMatrixNonrealExteriorCount_eq_two_upper {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) :
    matrixNonrealExteriorRootCount (A.map Complex.ofRealHom) r =
      2*realMatrixUpperNonrealExteriorCount A r := by
  classical
  have hsplit := multiset_nonreal_exterior_count_split
    ((A.map Complex.ofRealHom).charpoly.roots) r
  have heq := realMatrixUpperLowerNonrealCount_equal A r
  simp only [matrixNonrealExteriorRootCount,
    realMatrixUpperNonrealExteriorCount,
    realMatrixLowerNonrealExteriorCount] at *
  omega

#print axioms realMatrixUpperLowerNonrealCount_equal
#print axioms realMatrixNonrealExteriorCount_eq_two_upper
end SpectralRadiusUpperTail
