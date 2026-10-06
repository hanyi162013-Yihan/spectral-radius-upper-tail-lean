import SpectralRadiusUpperTail.RealSchurComplexEigenplaneIndependent

namespace SpectralRadiusUpperTail
open scoped Matrix

lemma real_matrix_complex_mulVec_re_finite {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (v : ι → ℂ) :
    (fun i => (((A.map Complex.ofRealHom).mulVec v) i).re) = A.mulVec (fun i => (v i).re) := by
  funext i
  simp [Matrix.mulVec,dotProduct,Complex.re_sum,Complex.mul_re]

lemma real_matrix_complex_mulVec_im_finite {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (v : ι → ℂ) :
    (fun i => (((A.map Complex.ofRealHom).mulVec v) i).im) = A.mulVec (fun i => (v i).im) := by
  funext i
  simp [Matrix.mulVec,dotProduct,Complex.im_sum,Complex.mul_im]


/-- A complex eigenvector of a real matrix gives two real vectors on
which the matrix acts by the real 2×2 block of its eigenvalue. -/
theorem realMatrix_complexEigenvector_re_im_finite
    {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (z : ι → ℂ) (ζ : ℂ)
    (hz : (A.map Complex.ofRealHom).mulVec z = ζ • z) :
    A.mulVec (fun i => (z i).re) =
        ζ.re • (fun i => (z i).re) - ζ.im • (fun i => (z i).im) ∧
      A.mulVec (fun i => (z i).im) =
        ζ.im • (fun i => (z i).re) + ζ.re • (fun i => (z i).im) := by
  constructor
  · funext i
    have hi := congrArg Complex.re (congrFun hz i)
    calc
      (A.mulVec (fun j => (z j).re)) i =
          (((A.map Complex.ofRealHom).mulVec z) i).re :=
        congrFun (real_matrix_complex_mulVec_re_finite A z).symm i
      _ = (ζ * z i).re := by simpa [Pi.smul_apply, smul_eq_mul] using hi
      _ = (ζ.re • (fun j => (z j).re) -
          ζ.im • (fun j => (z j).im)) i := by
        simp [Complex.mul_re, Pi.smul_apply, smul_eq_mul]
  · funext i
    have hi := congrArg Complex.im (congrFun hz i)
    calc
      (A.mulVec (fun j => (z j).im)) i =
          (((A.map Complex.ofRealHom).mulVec z) i).im :=
        congrFun (real_matrix_complex_mulVec_im_finite A z).symm i
      _ = (ζ * z i).im := by simpa [Pi.smul_apply, smul_eq_mul] using hi
      _ = (ζ.im • (fun j => (z j).re) +
          ζ.re • (fun j => (z j).im)) i := by
        simp [Complex.mul_im, Pi.smul_apply, smul_eq_mul]
        ring


/-- The real and imaginary parts of a nonzero eigenvector for a nonreal
eigenvalue of a real matrix are linearly independent over the reals.
This supplies the genuine invariant plane for a 2×2 real-Schur block. -/
theorem realMatrix_nonrealEigenvector_re_im_independent_finite
    {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ)
    (z : ι → ℂ) (ζ : ℂ)
    (hz : (A.map Complex.ofRealHom).mulVec z = ζ • z)
    (hz0 : z ≠ 0) (hIm : ζ.im ≠ 0) :
    LinearIndependent ℝ ![(fun i => (z i).re), (fun i => (z i).im)] := by
  let u : ι → ℝ := fun i => (z i).re
  let v : ι → ℝ := fun i => (z i).im
  have hpair := realMatrix_complexEigenvector_re_im_finite A z ζ hz
  change A.mulVec u = ζ.re • u - ζ.im • v ∧
    A.mulVec v = ζ.im • u + ζ.re • v at hpair
  have hu : u ≠ 0 := by
    intro hu0
    have hbw : ζ.im • v = 0 := by
      simpa [hu0] using hpair.1.symm
    have hv : v = 0 := (smul_eq_zero.mp hbw).resolve_left hIm
    apply hz0
    funext i
    apply Complex.ext
    · simpa [u] using congrFun hu0 i
    · simpa [v] using congrFun hv i
  have hnomul : ∀ a : ℝ, a • u ≠ v := by
    intro a ha
    have hv : v = a • u := ha.symm
    have hA : A.mulVec v = a • A.mulVec u := by
      rw [hv, Matrix.mulVec_smul]
    have ⟨i,hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hu
      funext i
      exact hn i
    have h1 := congrFun hpair.1 i
    have h2 := congrFun hpair.2 i
    have hAi := congrFun hA i
    have hvi := congrFun hv i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 hAi hvi
    rw [h1,h2,hvi] at hAi
    have hkey : ζ.im * (1+a^2) * u i = 0 := by nlinarith only [hAi]
    have hpos : (0:ℝ) < 1+a^2 := by positivity
    exact (mul_ne_zero (mul_ne_zero hIm (ne_of_gt hpos)) hi) hkey
  exact (LinearIndependent.pair_iff' hu).mpr hnomul


#print axioms realMatrix_complexEigenvector_re_im_finite
#print axioms realMatrix_nonrealEigenvector_re_im_independent_finite
end SpectralRadiusUpperTail
