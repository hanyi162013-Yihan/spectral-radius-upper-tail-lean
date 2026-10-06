import SpectralRadiusUpperTail.GaussianPrincipalPermutationVariance
import SpectralRadiusUpperTail.FiniteOrthogonalSecondMoment
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

/-- Exact finite Parseval identity for every weighted sum of principal
minor permutation monomials of an iid standard real Gaussian matrix. -/
theorem gaussian_principalPermutation_parseval
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : PrincipalPermutation ι → ℝ) :
    Integrable (fun x : ι × ι → ℝ =>
      (∑ p : PrincipalPermutation ι,
        c p * principalPermutationWord p x)^2)
      (Measure.pi (fun _ => standardNormal)) ∧
    (∫ x : ι × ι → ℝ,
      (∑ p : PrincipalPermutation ι,
        c p * principalPermutationWord p x)^2
      ∂Measure.pi (fun _ => standardNormal)) =
      ∑ p : PrincipalPermutation ι, (c p)^2 := by
  classical
  have hi (p q : PrincipalPermutation ι) :
      Integrable (fun x : ι × ι → ℝ =>
        (c p * principalPermutationWord p x) *
          (c q * principalPermutationWord q x))
        (Measure.pi (fun _ => standardNormal)) := by
    have h := (gaussian_principalPermutation_word_pair_integrable p q).const_mul
      (c p*c q)
    convert h using 1
    funext x
    ring
  have ho (p q : PrincipalPermutation ι) (hpq : p ≠ q) :
      (∫ x : ι × ι → ℝ,
        (c p * principalPermutationWord p x) *
          (c q * principalPermutationWord q x)
        ∂Measure.pi (fun _ => standardNormal)) = 0 := by
    have he (x : ι × ι → ℝ) :
        (c p * principalPermutationWord p x) *
          (c q * principalPermutationWord q x) =
        (c p*c q) *
          (principalPermutationWord p x * principalPermutationWord q x) := by ring
    simp_rw [he]
    rw [integral_const_mul,
      gaussian_principalPermutation_words_cross_zero p q hpq, mul_zero]
  obtain ⟨hint,heq⟩ := finite_orthogonal_second_moment
    (Measure.pi (fun _ : ι × ι => standardNormal))
    (fun p x => c p * principalPermutationWord p x) hi ho
  refine ⟨hint, heq.trans ?_⟩
  apply Finset.sum_congr rfl
  intro p hp
  simp_rw [mul_pow]
  rw [integral_const_mul, gaussian_principalPermutation_word_variance_one p,
    mul_one]

#print axioms gaussian_principalPermutation_parseval
end SpectralRadiusUpperTail
