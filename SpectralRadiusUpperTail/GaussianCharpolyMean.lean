import SpectralRadiusUpperTail.GaussianPrincipalMinorMoment
import SpectralRadiusUpperTail.CharpolyPrincipalMinorEvaluation
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix BigOperators

/-- Every principal minor of a finite iid Gaussian matrix is integrable. -/
theorem gaussian_principalMinor_integrable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) :
    Integrable (fun z : ι × ι → ℝ =>
      ((Matrix.of z.curry).submatrix
        (Subtype.val : s → ι) (Subtype.val : s → ι)).det)
      (Measure.pi (fun _ => standardNormal)) := by
  simp_rw [principalMinor_det_eq_gaussianPermutation_sum s]
  apply integrable_finsetSum
  intro π hπ
  have hi := gaussian_principalPermutation_word_pair_integrable
    (⟨s,π⟩ : PrincipalPermutation ι)
    (⟨∅,Equiv.refl (∅ : Finset ι)⟩ : PrincipalPermutation ι)
  have hw : Integrable (principalPermutationWord
      (⟨s,π⟩ : PrincipalPermutation ι))
      (Measure.pi (fun _ => standardNormal)) := by
    convert hi using 1
    funext z
    simp [principalPermutationWord]
  exact hw.const_mul _

/-- A finite Gaussian characteristic polynomial has finite first moment. -/
theorem gaussian_charpoly_integrable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ℝ) :
    Integrable (fun z : ι × ι → ℝ =>
      (Matrix.of z.curry).charpoly.eval x)
      (Measure.pi (fun _ => standardNormal)) := by
  classical
  simp_rw [charpoly_eval_eq_sum_principalMinors]
  apply integrable_finsetSum
  intro s hs
  exact (gaussian_principalMinor_integrable s).const_mul _

/-- The characteristic polynomial of an iid centered Gaussian matrix
has mean equal to its deterministic leading monomial. -/
theorem gaussian_charpoly_mean
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ℝ) :
    (∫ z : ι × ι → ℝ,
      (Matrix.of z.curry).charpoly.eval x
      ∂Measure.pi (fun _ => standardNormal)) =
      x^(Fintype.card ι) := by
  classical
  simp_rw [charpoly_eval_eq_sum_principalMinors]
  rw [integral_finsetSum]
  · rw [Finset.sum_eq_single ∅]
    · simp
    · intro s hs hne
      rw [integral_const_mul,
        gaussian_principalMinor_mean_zero s (Finset.nonempty_iff_ne_empty.mpr hne),
        mul_zero]
    · simp
  · intro s hs
    exact (gaussian_principalMinor_integrable s).const_mul _

#print axioms gaussian_principalMinor_integrable
#print axioms gaussian_charpoly_integrable
#print axioms gaussian_charpoly_mean
end SpectralRadiusUpperTail
