import SpectralRadiusUpperTail.GaussianPrincipalPermutationWords
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

/-- Every determinant permutation monomial has Gaussian variance one. -/
theorem gaussian_principalPermutation_word_variance_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : PrincipalPermutation ι) :
    (∫ x : ι × ι → ℝ,
      (principalPermutationWord p x)^2
      ∂Measure.pi (fun _ => standardNormal)) = 1 := by
  change (∫ x : ι × ι → ℝ,
      (∏ j : p.1, x (principalPermutationEdge p j))^2
      ∂Measure.pi (fun _ => standardNormal)) = 1
  rw [iid_simple_word_second_moment standardNormal
    (principalPermutationEdge p) (principalPermutationEdge_injective p),
    standardNormal_second_moment, one_pow]

/-- Products of any two determinant monomials are integrable under
the finite Gaussian matrix law. -/
theorem gaussian_principalPermutation_word_pair_integrable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : PrincipalPermutation ι) :
    Integrable (fun x : ι × ι → ℝ =>
      principalPermutationWord p x * principalPermutationWord q x)
      (Measure.pi (fun _ => standardNormal)) := by
  exact iid_real_word_pair_integrable standardNormal
    standardNormal_pow_integrable
    (principalPermutationEdge p) (principalPermutationEdge q)

#print axioms gaussian_principalPermutation_word_variance_one
#print axioms gaussian_principalPermutation_word_pair_integrable
end SpectralRadiusUpperTail
