import SpectralRadiusUpperTail.RealPairNonrealCoordinates

namespace SpectralRadiusUpperTail

theorem realPair_charpoly_center_height (B : Matrix (Fin 2) (Fin 2) ℝ) :
    B.charpoly = Polynomial.X^2-Polynomial.C (2*realPairCenter B)*Polynomial.X+
      Polynomial.C ((realPairCenter B)^2+realPairHeightSq B) := by
  rw [Matrix.charpoly_fin_two,realPair_trace_eq_two_center]
  congr 2
  unfold realPairHeightSq
  ring

theorem realPair_complex_charpoly_eval (B : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ) :
    (B.charpoly.map Complex.ofRealHom).eval z =
      (z-(realPairCenter B : ℂ))^2+(realPairHeightSq B : ℂ) := by
  rw [realPair_charpoly_center_height]
  simp only [Polynomial.map_add,Polynomial.map_sub,Polynomial.map_pow,
    Polynomial.map_mul,Polynomial.map_X,Polynomial.map_C,Polynomial.eval_add,
    Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_mul,Polynomial.eval_X,
    Polynomial.eval_C,Complex.ofRealHom_eq_coe,Complex.ofReal_mul,
    Complex.ofReal_ofNat,Complex.ofReal_add,Complex.ofReal_pow]
  ring

/-- A nonreal root determines both coefficients of a real quadratic. -/
theorem realPair_nonreal_root_data (B : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ)
    (hz : (B.charpoly.map Complex.ofRealHom).eval z=0) (hi : z.im ≠ 0) :
    realPairCenter B=z.re ∧ realPairHeightSq B=z.im^2 := by
  rw [realPair_complex_charpoly_eval] at hz
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [pow_two,Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.sub_im,Complex.ofReal_im,Complex.zero_re,sub_zero] at hre
  simp only [pow_two,Complex.add_im,Complex.sub_re,Complex.mul_im,Complex.ofReal_re,
    Complex.sub_im,Complex.ofReal_im,Complex.zero_im,sub_zero,add_zero] at him
  have hp : (z.re-realPairCenter B)*z.im=0 := by nlinarith only [him]
  have hc : realPairCenter B=z.re :=
    (sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hi)).symm
  refine ⟨hc,?_⟩
  rw [hc] at hre
  nlinarith only [hre]

theorem realPair_charpoly_eq_of_shared_nonreal_root
    (A B : Matrix (Fin 2) (Fin 2) ℝ) (z : ℂ)
    (hA : (A.charpoly.map Complex.ofRealHom).eval z=0)
    (hB : (B.charpoly.map Complex.ofRealHom).eval z=0) (hi : z.im ≠ 0) :
    A.charpoly=B.charpoly := by
  obtain ⟨ha,ha'⟩ := realPair_nonreal_root_data A z hA hi
  obtain ⟨hb,hb'⟩ := realPair_nonreal_root_data B z hB hi
  rw [realPair_charpoly_center_height,realPair_charpoly_center_height,ha,ha',hb,hb']

theorem realPair_nonreal_lower_entry_ne_zero
    (B : Matrix (Fin 2) (Fin 2) ℝ) (hB : 0 < realPairHeightSq B) : B 1 0 ≠ 0 := by
  intro hzero
  unfold realPairHeightSq realPairCenter at hB
  rw [Matrix.det_fin_two,Matrix.trace_fin_two,hzero,mul_zero,sub_zero] at hB
  nlinarith [sq_nonneg (B 0 0-B 1 1)]

#print axioms realPair_charpoly_center_height
#print axioms realPair_complex_charpoly_eval
#print axioms realPair_nonreal_root_data
#print axioms realPair_charpoly_eq_of_shared_nonreal_root
#print axioms realPair_nonreal_lower_entry_ne_zero
end SpectralRadiusUpperTail
