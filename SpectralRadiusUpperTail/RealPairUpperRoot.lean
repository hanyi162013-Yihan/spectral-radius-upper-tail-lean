import SpectralRadiusUpperTail.RealPairComplexRootData

namespace SpectralRadiusUpperTail

noncomputable def realPairUpperRoot (B : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  (realPairCenter B : ℂ)+(realPairHeight B : ℂ)*Complex.I

theorem realPairUpperRoot_im (B : Matrix (Fin 2) (Fin 2) ℝ) :
    (realPairUpperRoot B).im=realPairHeight B := by simp [realPairUpperRoot]

theorem realPairUpperRoot_pos (B : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : 0 < realPairHeightSq B) : 0 < (realPairUpperRoot B).im := by
  rw [realPairUpperRoot_im]
  exact Real.sqrt_pos.mpr hB

theorem realPairUpperRoot_isRoot (B : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : 0 ≤ realPairHeightSq B) :
    (B.charpoly.map Complex.ofRealHom).eval (realPairUpperRoot B)=0 := by
  rw [realPair_complex_charpoly_eval]
  have hy := realPairHeight_sq B hB
  apply Complex.ext
  · simp [realPairUpperRoot,pow_two,Complex.mul_re]
    nlinarith only [hy]
  · simp [realPairUpperRoot,pow_two,Complex.mul_im]

theorem realPairUpperRoot_eq_of_root (B : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ)
    (hz : (B.charpoly.map Complex.ofRealHom).eval z=0) (hi : 0 < z.im) :
    realPairUpperRoot B=z := by
  obtain ⟨hc,hh⟩ := realPair_nonreal_root_data B z hz (ne_of_gt hi)
  apply Complex.ext
  · simp [realPairUpperRoot,hc]
  · rw [realPairUpperRoot_im]
    simp [realPairHeight,hh,Real.sqrt_sq_eq_abs,abs_of_pos hi]

theorem realPairUpperRoot_continuous : Continuous realPairUpperRoot := by
  unfold realPairUpperRoot realPairHeight realPairHeightSq realPairCenter
  fun_prop

theorem realPairUpperRoot_eq_of_charpoly
    (A B : Matrix (Fin 2) (Fin 2) ℝ) (hpoly : A.charpoly=B.charpoly)
    (hA : 0 < realPairHeightSq A) : realPairUpperRoot A=realPairUpperRoot B := by
  apply Eq.symm
  apply realPairUpperRoot_eq_of_root B (realPairUpperRoot A)
  · rw [← hpoly]
    exact realPairUpperRoot_isRoot A hA.le
  · exact realPairUpperRoot_pos A hA

#print axioms realPairUpperRoot_im
#print axioms realPairUpperRoot_pos
#print axioms realPairUpperRoot_isRoot
#print axioms realPairUpperRoot_eq_of_root
#print axioms realPairUpperRoot_continuous
#print axioms realPairUpperRoot_eq_of_charpoly
end SpectralRadiusUpperTail
