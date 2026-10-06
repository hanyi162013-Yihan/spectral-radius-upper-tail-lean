import SpectralRadiusUpperTail.ComplexCharpolyPrincipalMinorEvaluation
import SpectralRadiusUpperTail.GaussianComplexWeightedPrincipalMinorParseval
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix BigOperators

/-- The exact modulus-square moment of the complex characteristic polynomial
of an iid *real* Gaussian matrix. Only Gaussian entry orthogonality is used. -/
theorem gaussian_real_complex_charpoly_second_moment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ℂ) :
    Integrable (fun z : ι × ι → ℝ =>
      Complex.normSq
        (((Matrix.of z.curry).map Complex.ofRealHom).charpoly.eval w))
      (Measure.pi (fun _ => standardNormal)) ∧
    (∫ z : ι × ι → ℝ,
      Complex.normSq
        (((Matrix.of z.curry).map Complex.ofRealHom).charpoly.eval w)
      ∂Measure.pi (fun _ => standardNormal)) =
      ∑ s : Finset ι,
        (Complex.normSq w)^(Fintype.card ι-s.card) *
          (s.card.factorial : ℝ) := by
  classical
  let N := Fintype.card ι
  let a : Finset ι → ℂ := fun s =>
    (-1 : ℂ)^s.card * w^(N-s.card)
  have he (z : ι × ι → ℝ) :
      ((Matrix.of z.curry).map Complex.ofRealHom).charpoly.eval w =
      ∑ s : Finset ι, a s *
        (((Matrix.of z.curry).submatrix
          (Subtype.val : s → ι) (Subtype.val : s → ι)).det : ℂ) :=
    real_charpoly_complex_eval_eq_sum_principalMinors _ w
  have h := gaussian_complex_weighted_principalMinor_parseval a
  constructor
  · simpa only [he] using h.1
  · simp_rw [he]
    rw [h.2]
    apply Finset.sum_congr rfl
    intro s hs
    dsimp [a, N]
    simp [map_mul, map_pow]

#print axioms gaussian_real_complex_charpoly_second_moment
end SpectralRadiusUpperTail
