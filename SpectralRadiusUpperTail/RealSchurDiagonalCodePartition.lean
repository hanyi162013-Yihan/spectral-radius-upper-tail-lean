import SpectralRadiusUpperTail.RealSchurDiagonalSimpleAE
import SpectralRadiusUpperTail.RealSchurMixedFlagFullFiber

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal

theorem lintegral_finite_code_partition
    {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (P : X → Prop) (c : X → ι)
    (hP : ∀ᵐ x ∂μ, P x)
    (hS : ∀ i, MeasurableSet {x | P x ∧ c x=i}) (f : X → ℝ≥0∞) :
    (∑ i, ∫⁻ x in {x | P x ∧ c x=i}, f x ∂μ) = ∫⁻ x, f x ∂μ := by
  classical
  let S := fun i => {x | P x ∧ c x=i}
  have hdis : Pairwise (fun i j => Disjoint (S i) (S j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hij (hx.2.symm.trans hy.2)
  have hu : (⋃ i, S i)={x | P x} := by
    ext x
    simp [S]
  have hPm : MeasurableSet {x | P x} := hu ▸ MeasurableSet.iUnion hS
  have hsum : (∑ i, ∫⁻ x in S i, f x ∂μ)=(∑' i, ∫⁻ x in S i, f x ∂μ) :=
    (tsum_fintype _).symm
  change (∑ i, ∫⁻ x in S i, f x ∂μ)=_
  rw [hsum]
  rw [← lintegral_iUnion hS hdis,hu,← lintegral_indicator hPm]
  apply lintegral_congr_ae
  filter_upwards [hP] with x hx
  exact Set.indicator_of_mem hx f

theorem realSchurMixedDiagonalCodeSource_integral_sum
    {m : ℕ} (s : Fin m → ℕ)
    (f : (RealSchurMixedDiagonalEntry s → ℝ) → ℝ≥0∞) :
    (∑ code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool,
      ∫⁻ d in realSchurMixedDiagonalCodeSource s code, f d) = ∫⁻ d, f d := by
  exact lintegral_finite_code_partition volume
    (fun d => (realSchurMixedUpperEntryJoin s d 0).charpoly.Separable)
    (fun d => realSchurMixedSpectralCode s (realSchurMixedUpperEntryJoin s d 0))
    (realSchurMixedDiagonal_simpleSpectrum_ae s)
    (measurableSet_realSchurMixedDiagonalCodeSource s) f

#print axioms lintegral_finite_code_partition
#print axioms realSchurMixedDiagonalCodeSource_integral_sum
end SpectralRadiusUpperTail
