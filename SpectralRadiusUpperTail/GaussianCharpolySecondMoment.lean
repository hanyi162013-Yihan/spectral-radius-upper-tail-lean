import SpectralRadiusUpperTail.CharpolyPrincipalMinorEvaluation
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix BigOperators

/-- An exact finite-dimensional covariance identity for the real
Gaussian characteristic polynomial, before grouping by minor size. -/
theorem gaussian_charpoly_second_moment_principalMinorSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ℝ) :
    Integrable (fun z : ι × ι → ℝ =>
      ((Matrix.of z.curry).charpoly.eval x)^2)
      (Measure.pi (fun _ => standardNormal)) ∧
    (∫ z : ι × ι → ℝ,
      ((Matrix.of z.curry).charpoly.eval x)^2
      ∂Measure.pi (fun _ => standardNormal)) =
      ∑ s : Finset ι,
        (x^(2*(Fintype.card ι-s.card))) * (s.card.factorial : ℝ) := by
  classical
  let a : Finset ι → ℝ :=
    fun s => (-1 : ℝ)^s.card * x^(Fintype.card ι-s.card)
  have he (z : ι × ι → ℝ) :
      (Matrix.of z.curry).charpoly.eval x =
        ∑ s : Finset ι, a s *
          ((Matrix.of z.curry).submatrix
            (Subtype.val : s → ι) (Subtype.val : s → ι)).det :=
    charpoly_eval_eq_sum_principalMinors _ x
  have h := gaussian_weighted_principalMinor_parseval a
  constructor
  · simpa only [he] using h.1
  · simp_rw [he]
    rw [h.2]
    apply Finset.sum_congr rfl
    intro s hs
    dsimp [a]
    have hsign : ((-1 : ℝ)^s.card)^2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    rw [mul_pow, hsign, one_mul]
    congr 1
    rw [← pow_mul]
    congr 1
    omega

#print axioms gaussian_charpoly_second_moment_principalMinorSum
end SpectralRadiusUpperTail
