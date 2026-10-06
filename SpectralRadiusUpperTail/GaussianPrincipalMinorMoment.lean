import SpectralRadiusUpperTail.GaussianPermutationSign
import SpectralRadiusUpperTail.GaussianPrincipalPermutationMean
import SpectralRadiusUpperTail.FiniteOrthogonalSecondMoment
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix BigOperators

/-- The determinant of every nonempty principal Gaussian minor has mean zero. -/
theorem gaussian_principalMinor_mean_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) :
    (∫ x : ι × ι → ℝ,
      ((Matrix.of x.curry).submatrix
        (Subtype.val : s → ι) (Subtype.val : s → ι)).det
      ∂Measure.pi (fun _ => standardNormal)) = 0 := by
  simp_rw [principalMinor_det_eq_gaussianPermutation_sum s]
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
    apply Finset.sum_eq_zero
    intro π hπ
    rw [gaussian_principalPermutation_word_mean_zero (⟨s,π⟩ : PrincipalPermutation ι) hs,
      mul_zero]
  · intro π hπ
    have hi := gaussian_principalPermutation_word_pair_integrable
      (⟨s,π⟩ : PrincipalPermutation ι)
      (⟨∅,Equiv.refl (∅ : Finset ι)⟩ : PrincipalPermutation ι)
    have hw : Integrable (principalPermutationWord
        (⟨s,π⟩ : PrincipalPermutation ι))
        (Measure.pi (fun _ => standardNormal)) := by
      convert hi using 1
      funext x
      simp [principalPermutationWord]
    exact hw.const_mul _

/-- The squared determinant of a principal Gaussian minor has factorial mean. -/
theorem gaussian_principalMinor_second_moment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) :
    (∫ x : ι × ι → ℝ,
      (((Matrix.of x.curry).submatrix
        (Subtype.val : s → ι) (Subtype.val : s → ι)).det)^2
      ∂Measure.pi (fun _ => standardNormal)) = (s.card.factorial : ℝ) := by
  classical
  let c : Equiv.Perm s → ℝ := fun π => ((Equiv.Perm.sign π : ℤ) : ℝ)
  let F : Equiv.Perm s → (ι × ι → ℝ) → ℝ :=
    fun π x => c π * principalPermutationWord (⟨s,π⟩ : PrincipalPermutation ι) x
  have hi (π τ : Equiv.Perm s) :
      Integrable (fun x : ι × ι → ℝ => F π x * F τ x)
        (Measure.pi (fun _ => standardNormal)) := by
    have h := (gaussian_principalPermutation_word_pair_integrable
      (⟨s,π⟩ : PrincipalPermutation ι)
      (⟨s,τ⟩ : PrincipalPermutation ι)).const_mul (c π * c τ)
    convert h using 1
    funext x
    dsimp [F]
    ring
  have ho (π τ : Equiv.Perm s) (hπτ : π ≠ τ) :
      (∫ x : ι × ι → ℝ, F π x * F τ x
        ∂Measure.pi (fun _ => standardNormal)) = 0 := by
    have hpq : (⟨s,π⟩ : PrincipalPermutation ι) ≠ ⟨s,τ⟩ := by
      intro h
      cases h
      exact hπτ rfl
    have he (x : ι × ι → ℝ) :
        F π x * F τ x = (c π * c τ) *
          (principalPermutationWord (⟨s,π⟩ : PrincipalPermutation ι) x *
            principalPermutationWord (⟨s,τ⟩ : PrincipalPermutation ι) x) := by
      dsimp [F]
      ring
    simp_rw [he]
    rw [integral_const_mul,
      gaussian_principalPermutation_words_cross_zero _ _ hpq, mul_zero]
  obtain ⟨_, heq⟩ := finite_orthogonal_second_moment
    (Measure.pi (fun _ : ι × ι => standardNormal)) F hi ho
  simp_rw [principalMinor_det_eq_gaussianPermutation_sum s]
  change (∫ x, (∑ π, F π x)^2 ∂Measure.pi (fun _ => standardNormal)) = _
  rw [heq]
  have hπ (π : Equiv.Perm s) :
      (∫ x : ι × ι → ℝ, (F π x)^2
        ∂Measure.pi (fun _ => standardNormal)) = 1 := by
    simp_rw [show ∀ x : ι × ι → ℝ,
        (F π x)^2 = (c π)^2 *
          (principalPermutationWord (⟨s,π⟩ : PrincipalPermutation ι) x)^2
        from fun x => mul_pow ..]
    rw [integral_const_mul,
      gaussian_principalPermutation_word_variance_one,
      mul_one]
    exact real_perm_sign_sq_one π
  simp_rw [hπ]
  simp [Fintype.card_perm, Fintype.card_coe]

end SpectralRadiusUpperTail
