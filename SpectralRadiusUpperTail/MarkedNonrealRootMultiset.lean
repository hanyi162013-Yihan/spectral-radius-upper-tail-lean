import SpectralRadiusUpperTail.MarkedNonrealRootWeight
import SpectralRadiusUpperTail.RealMatrixNonrealPairPower
import SpectralRadiusUpperTail.MatrixCharpolyScalarRoots

namespace SpectralRadiusUpperTail
open Classical
open scoped ENNReal Matrix

theorem markedNonrealRootWeight_eq_roots
    (m : ℕ) (A : Matrix (MarkedNonrealIndex m) (MarkedNonrealIndex m) ℝ)
    (hA : A.charpoly.Separable) (g : ℂ → ℝ≥0∞) :
    markedNonrealRootWeight m A g=
      ((A.charpoly.map Complex.ofRealHom).roots.map
        (fun z => if 0 < z.im then g z else 0)).sum := by
  rw [realSchurMixedCanonicalSpectrum_roots (markedNonrealBlockSizes m) A hA,Multiset.map_map]
  rfl

theorem multiset_ofReal_sum_map_nonneg {α : Type*}
    (s : Multiset α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ENNReal.ofReal (s.map f).sum=(s.map (fun a => ENNReal.ofReal (f a))).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons,Multiset.sum_cons]
    rw [ENNReal.ofReal_add (hf a)
      (Multiset.sum_nonneg (by intro b hb; obtain ⟨x,hx,rfl⟩ := Multiset.mem_map.mp hb; exact hf x)),ih]

/-- A positive real scaling preserves the choice of the upper conjugate
root and acts only on the exterior radial weight. -/
theorem realMatrixUpperNonrealExteriorPower_scaled_roots
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (hc : 0 < c) (k : ℕ) :
    ENNReal.ofReal (realMatrixUpperNonrealExteriorPower (c • A) k)=
      ((A.charpoly.map Complex.ofRealHom).roots.map (fun z : ℂ =>
        if 0 < z.im then
          (if 1 < ‖c • z‖ then ENNReal.ofReal (‖c • z‖^(2*k)) else 0)
        else 0)).sum := by
  have hm : (c • A).map Complex.ofRealHom=(c : ℂ) • (A.map Complex.ofRealHom) := by
    ext i j
    simp [Matrix.smul_apply,Matrix.map_apply,smul_eq_mul]
  unfold realMatrixUpperNonrealExteriorPower
  rw [hm,matrix_charpoly_smul_roots _ (c : ℂ) (by exact_mod_cast hc.ne'),
    Matrix.charpoly_map,Multiset.map_map,multiset_ofReal_sum_map_nonneg]
  · congr 1
    apply Multiset.map_congr rfl
    intro z hz
    have him : 0 < ((c : ℂ)*z).im ↔ 0 < z.im := by
      simp [Complex.mul_im,mul_pos_iff_of_pos_left hc]
    change ENNReal.ofReal (if 0 < ((c : ℂ)*z).im ∧ 1 < ‖(c : ℂ)*z‖
      then ‖(c : ℂ)*z‖^(2*k) else 0)=_
    simp only [him]
    simp only [← Complex.real_smul]
    by_cases hi : 0 < z.im <;> by_cases hr : 1 < ‖c • z‖ <;>
      simp only [hi,hr,and_true,true_and,false_and,ite_true,ite_false,ENNReal.ofReal_zero]
  · intro z
    dsimp only [Function.comp_def]
    split_ifs
    · exact pow_nonneg (norm_nonneg _) _
    · exact le_rfl

#print axioms markedNonrealRootWeight_eq_roots
#print axioms multiset_ofReal_sum_map_nonneg
#print axioms realMatrixUpperNonrealExteriorPower_scaled_roots
end SpectralRadiusUpperTail
