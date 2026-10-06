import SpectralRadiusUpperTail.ShiftedDeterminantRoots

namespace SpectralRadiusUpperTail
open scoped BigOperators

/-- The unregularized exterior log-determinant, normalized by the matrix dimension. -/
noncomputable def normalizedExteriorLogDet {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (b : ℝ) : ℝ := Real.log ‖Matrix.det ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)-A)‖/(n : ℝ)

lemma exteriorLogDet_normalization {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (b M : ℝ) (hM : 0 ≤ M) (hb : M < b)
    (hA : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖ ≤ M) :
    Real.log (b-M) ≤ normalizedExteriorLogDet A b ∧
      normalizedExteriorLogDet A b ≤ Real.log (b+M) := by
  have hb0 : 0 < b := hM.trans_lt hb
  have hlo : 0 < b-M := sub_pos.mpr hb
  have hroots (w : ℂ) (hw : w ∈ A.charpoly.roots) :
      b-M ≤ ‖(b : ℂ)-w‖ ∧ ‖(b : ℂ)-w‖ ≤ b+M := by
    have hwM := (charpoly_root_norm_le_operator hn A w hw).trans hA
    have hbn : ‖(b : ℂ)‖ = b := by simp [abs_of_pos hb0]
    constructor
    · have hh := norm_sub_norm_le (b : ℂ) w
      rw [hbn] at hh
      linarith
    · calc
        _ ≤ ‖(b : ℂ)‖+‖w‖ := norm_sub_le _ _
        _ ≤ b+M := by rw [hbn]; linarith
  have hz (w : ℂ) (hw : w ∈ A.charpoly.roots) : (b : ℂ) ≠ w := by
    exact sub_ne_zero.mp (norm_pos_iff.mp (hlo.trans_le (hroots w hw).1))
  have hcard : A.charpoly.roots.card = n := by
    rw [← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots,
      Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hl : (n : ℝ)*Real.log (b-M) ≤
      (A.charpoly.roots.map (fun w => Real.log ‖(b : ℂ)-w‖)).sum := by
    have hh := Multiset.sum_map_le_sum_map (s := A.charpoly.roots)
      (fun _ => Real.log (b-M)) (fun w => Real.log ‖(b : ℂ)-w‖)
      (fun w hw => Real.log_le_log hlo (hroots w hw).1)
    simpa [Multiset.map_const, hcard, nsmul_eq_mul] using hh
  have hu : (A.charpoly.roots.map (fun w => Real.log ‖(b : ℂ)-w‖)).sum ≤
      (n : ℝ)*Real.log (b+M) := by
    have hh := Multiset.sum_map_le_sum_map (s := A.charpoly.roots)
      (fun w => Real.log ‖(b : ℂ)-w‖) (fun _ => Real.log (b+M))
      (fun w hw => Real.log_le_log (hlo.trans_le (hroots w hw).1) (hroots w hw).2)
    simpa [Multiset.map_const, hcard, nsmul_eq_mul] using hh
  unfold normalizedExteriorLogDet
  rw [shiftedDeterminant_log_norm A b hz]
  constructor
  · exact (le_div_iff₀ (Nat.cast_pos.mpr hn)).mpr (by simpa only [mul_comm] using hl)
  · exact (div_le_iff₀ (Nat.cast_pos.mpr hn)).mpr (by simpa only [mul_comm] using hu)

#print axioms normalizedExteriorLogDet
#print axioms exteriorLogDet_normalization
end SpectralRadiusUpperTail
