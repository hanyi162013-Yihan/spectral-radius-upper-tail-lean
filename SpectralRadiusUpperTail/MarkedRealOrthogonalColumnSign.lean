import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

/-- Two positive-oriented unit columns on the same real line are equal.
This removes the sign ambiguity in a projective angular chart. -/
theorem orthogonal_firstColumns_eq_of_collinear_positive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι) (Q R : Matrix ι ι ℝ)
    (hQ : Qᵀ*Q=1) (hR : Rᵀ*R=1)
    (c : ℝ) (hcol : ∀ i, R i e = c * Q i e)
    (hQpos : 0 < Q e e) (hRpos : 0 < R e e) :
    ∀ i, R i e = Q i e := by
  have hnormQ : (∑ i : ι, (Q i e)^2) = 1 := by
    have h := congrArg (fun M : Matrix ι ι ℝ => M e e) hQ
    simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using h
  have hnormR : (∑ i : ι, (R i e)^2) = 1 := by
    have h := congrArg (fun M : Matrix ι ι ℝ => M e e) hR
    simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using h
  have hc2 : c^2 = 1 := by
    calc
      c^2 = c^2 * (∑ i : ι, (Q i e)^2) := by rw [hnormQ, mul_one]
      _ = ∑ i : ι, (R i e)^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hcol i]
        ring
      _ = 1 := hnormR
  have hcpos : 0 < c := by
    have he := hcol e
    nlinarith
  have hc : c = 1 := by nlinarith
  intro i
  simpa [hc] using hcol i

#print axioms orthogonal_firstColumns_eq_of_collinear_positive
end SpectralRadiusUpperTail
