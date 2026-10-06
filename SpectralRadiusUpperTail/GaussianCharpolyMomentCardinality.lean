import SpectralRadiusUpperTail.GaussianCharpolySecondMoment
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators

/-- Group the exact Gaussian characteristic-polynomial second moment
by the cardinality of the chosen principal minor. -/
theorem gaussian_charpoly_second_moment_cardinality
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ℝ) :
    (∫ z : ι × ι → ℝ,
      ((Matrix.of z.curry).charpoly.eval x)^2
      ∂Measure.pi (fun _ => standardNormal)) =
      ∑ k ∈ Finset.range (Fintype.card ι + 1),
        (((Fintype.card ι).choose k * k.factorial : ℕ) : ℝ) *
          x^(2*(Fintype.card ι-k)) := by
  classical
  rw [(gaussian_charpoly_second_moment_principalMinorSum x).2]
  rw [← sum_principalMinors_by_card
    (fun s : Finset ι => x^(2*(Fintype.card ι-s.card)) *
      (s.card.factorial : ℝ))]
  apply Finset.sum_congr rfl
  intro k hk
  have hterm (s : Finset ι)
      (hs : s ∈ (Finset.univ : Finset ι).powersetCard k) :
      x^(2*(Fintype.card ι-s.card)) * (s.card.factorial : ℝ) =
        x^(2*(Fintype.card ι-k)) * (k.factorial : ℝ) := by
    rw [(Finset.mem_powersetCard.mp hs).2]
  calc
    (∑ s ∈ (Finset.univ : Finset ι).powersetCard k,
      x^(2*(Fintype.card ι-s.card)) * (s.card.factorial : ℝ)) =
        ∑ s ∈ (Finset.univ : Finset ι).powersetCard k,
          x^(2*(Fintype.card ι-k)) * (k.factorial : ℝ) := by
            apply Finset.sum_congr rfl
            intro s hs
            exact hterm s hs
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_powersetCard,
        Finset.card_univ, nsmul_eq_mul]
      push_cast
      ring

#print axioms gaussian_charpoly_second_moment_cardinality
end SpectralRadiusUpperTail
