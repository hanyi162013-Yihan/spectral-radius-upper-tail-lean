import SpectralRadiusUpperTail.GaussianPrincipalMinorMoment
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix BigOperators

/-- Orthogonality of all Gaussian principal-minor determinants, with
an arbitrary scalar weight for each principal minor. -/
theorem gaussian_weighted_principalMinor_parseval
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Finset ι → ℝ) :
    Integrable (fun x : ι × ι → ℝ =>
      (∑ s : Finset ι, a s *
        ((Matrix.of x.curry).submatrix
          (Subtype.val : s → ι) (Subtype.val : s → ι)).det)^2)
      (Measure.pi (fun _ => standardNormal)) ∧
    (∫ x : ι × ι → ℝ,
      (∑ s : Finset ι, a s *
        ((Matrix.of x.curry).submatrix
          (Subtype.val : s → ι) (Subtype.val : s → ι)).det)^2
      ∂Measure.pi (fun _ => standardNormal)) =
      ∑ s : Finset ι, (a s)^2 * (s.card.factorial : ℝ) := by
  classical
  let c : PrincipalPermutation ι → ℝ :=
    fun p => a p.1 * ((Equiv.Perm.sign p.2 : ℤ) : ℝ)
  have he (x : ι × ι → ℝ) :
      (∑ s : Finset ι, a s *
        ((Matrix.of x.curry).submatrix
          (Subtype.val : s → ι) (Subtype.val : s → ι)).det) =
      ∑ p : PrincipalPermutation ι,
        c p * principalPermutationWord p x := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro s hs
    rw [principalMinor_det_eq_gaussianPermutation_sum s, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro π hπ
    dsimp [c]
    ring
  have hc := gaussian_principalPermutation_parseval c
  constructor
  · simpa only [he] using hc.1
  · simp_rw [he]
    rw [hc.2, Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro s hs
    have hterm (π : Equiv.Perm s) :
        (c (⟨s,π⟩ : PrincipalPermutation ι))^2 = (a s)^2 := by
      dsimp [c]
      rw [mul_pow, real_perm_sign_sq_one π, mul_one]
    simp_rw [hterm]
    simp [Fintype.card_perm, Fintype.card_coe, mul_comm]

#print axioms gaussian_weighted_principalMinor_parseval
end SpectralRadiusUpperTail
