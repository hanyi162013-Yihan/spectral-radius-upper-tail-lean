import SpectralRadiusUpperTail.GaussianComplexCharpolySecondMoment
import SpectralRadiusUpperTail.CharpolyPrincipalMinorEvaluation
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

/-- The real-Gaussian complex characteristic-polynomial second moment,
grouped by principal-minor size. -/
theorem gaussian_real_complex_charpoly_second_moment_cardinality
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ℂ) :
    (∫ z : ι × ι → ℝ,
      Complex.normSq
        (((Matrix.of z.curry).map Complex.ofRealHom).charpoly.eval w)
      ∂Measure.pi (fun _ => standardNormal)) =
      ∑ k ∈ Finset.range (Fintype.card ι+1),
        (((Fintype.card ι).choose k * k.factorial : ℕ) : ℝ) *
          (Complex.normSq w)^(Fintype.card ι-k) := by
  classical
  rw [(gaussian_real_complex_charpoly_second_moment w).2]
  rw [← sum_principalMinors_by_card
    (fun s : Finset ι =>
      (Complex.normSq w)^(Fintype.card ι-s.card) *
        (s.card.factorial : ℝ))]
  apply Finset.sum_congr rfl
  intro k hk
  have hterm (s : Finset ι)
      (hs : s ∈ (Finset.univ : Finset ι).powersetCard k) :
      (Complex.normSq w)^(Fintype.card ι-s.card) *
        (s.card.factorial : ℝ) =
      (Complex.normSq w)^(Fintype.card ι-k) *
        (k.factorial : ℝ) := by
    rw [(Finset.mem_powersetCard.mp hs).2]
  calc
    (∑ s ∈ (Finset.univ : Finset ι).powersetCard k,
      (Complex.normSq w)^(Fintype.card ι-s.card) *
        (s.card.factorial : ℝ)) =
        ∑ s ∈ (Finset.univ : Finset ι).powersetCard k,
          (Complex.normSq w)^(Fintype.card ι-k) *
            (k.factorial : ℝ) := by
          apply Finset.sum_congr rfl
          intro s hs
          exact hterm s hs
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_powersetCard,
        Finset.card_univ, nsmul_eq_mul]
      push_cast
      ring

#print axioms gaussian_real_complex_charpoly_second_moment_cardinality
end SpectralRadiusUpperTail
