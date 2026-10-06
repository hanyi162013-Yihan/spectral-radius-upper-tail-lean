import SpectralRadiusUpperTail.RealEuclideanEigenplane
import SpectralRadiusUpperTail.MarkedNonrealRegularFrame

namespace SpectralRadiusUpperTail
open scoped Matrix

theorem complex_self_quadratic_eval (z : ℂ) :
    ((Polynomial.X^2-Polynomial.C (2*z.re)*Polynomial.X+
      Polynomial.C (z.re^2+z.im^2)).map Complex.ofRealHom).eval z=0 := by
  simp only [Polynomial.map_add,Polynomial.map_sub,Polynomial.map_pow,
    Polynomial.map_mul,Polynomial.map_X,Polynomial.map_C,Polynomial.eval_add,
    Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_mul,Polynomial.eval_X,
    Polynomial.eval_C,Complex.ofRealHom_eq_coe,Complex.ofReal_mul,
    Complex.ofReal_ofNat,Complex.ofReal_add,Complex.ofReal_pow]
  apply Complex.ext <;>
    simp [pow_two,Complex.mul_re,Complex.mul_im] <;> ring

/-- Every prescribed nonreal root, rather than an unspecified first pair,
is represented by a regular marked-pair Schur frame. -/
theorem exists_markedNonrealRoot_regular_frame
    (m : ℕ) (hm : 0 < m)
    (A : Matrix (RealSchurMixedCoord (markedNonrealBlockSizes m))
      (RealSchurMixedCoord (markedNonrealBlockSizes m)) ℝ)
    (hsep : A.charpoly.Separable) (z : ℂ)
    (hz : (A.charpoly.map Complex.ofRealHom).IsRoot z) (hi : z.im ≠ 0) :
    ∃ c : RealSchurMixedRegularFrame (markedNonrealBlockSizes m),
      ((markedNonrealFirstBlock m c.T).charpoly.map Complex.ofRealHom).eval z=0 ∧
      A=c.Q*c.T*c.Qᵀ := by
  obtain ⟨P,hP,hInv,hpoly⟩ := realMatrix_nonrealRoot_euclidean_plane A z hz hi
  obtain ⟨c,hc,hrep⟩ := exists_markedNonreal_regular_frame m hm A hsep P hP hInv
  refine ⟨c,?_,hrep⟩
  rw [hc,hpoly]
  exact complex_self_quadratic_eval z

#print axioms complex_self_quadratic_eval
#print axioms exists_markedNonrealRoot_regular_frame
end SpectralRadiusUpperTail
