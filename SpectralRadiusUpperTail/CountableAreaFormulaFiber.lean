import SpectralRadiusUpperTail.CountableChartFiberCount
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

theorem countableChart_imageIndicators_eq_fiberCount
    {X Y : Type*} (f : X → Y) (s : ℕ → Set X)
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hinj : ∀ k, InjOn f (s k))
    (g : Y → ℝ≥0∞) (y : Y) :
    (∑' k, (f '' s k).indicator g y) =
      ((f ⁻¹' {y} ∩ ⋃ k, s k).encard : ℝ≥0∞) * g y := by
  let I : Set ℕ := {k | y ∈ f '' s k}
  have hsum : (∑' k, (f '' s k).indicator (fun _ => (1 : ℝ≥0∞)) y) =
      (I.encard : ℝ≥0∞) := by
    calc
      (∑' k, (f '' s k).indicator (fun _ => (1 : ℝ≥0∞)) y) =
          ∑' k, I.indicator (fun _ => (1 : ℝ≥0∞)) k := by
        congr 1
      _ = ∑' k : I, (1 : ℝ≥0∞) := (tsum_subtype I 1).symm
      _ = (I.encard : ℝ≥0∞) := ENNReal.tsum_set_one I
  calc
    (∑' k, (f '' s k).indicator g y) =
        ∑' k, (f '' s k).indicator (fun _ => (1 : ℝ≥0∞)) y * g y := by
      congr 1
      funext k
      by_cases hk : y ∈ f '' s k <;> simp [indicator, hk]
    _ = (∑' k, (f '' s k).indicator (fun _ => (1 : ℝ≥0∞)) y) * g y :=
      ENNReal.tsum_mul_right
    _ = ((f ⁻¹' {y} ∩ ⋃ k, s k).encard : ℝ≥0∞) * g y := by
      rw [hsum, countableChartFiber_encard f s hd hinj y]

/-- The chart area formula as a true finite-to-one fiber count. The
marked-eigenline application still has to identify these fibers with
real eigenvalue marks and evaluate the Gaussian coordinate integral. -/
theorem countable_local_area_formula_fiber_count
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E → E) (f' : E → E →L[ℝ] E)
    (s : ℕ → Set E) (hs : ∀ k, MeasurableSet (s k))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hf' : ∀ k x, x ∈ s k → HasFDerivWithinAt f (f' x) (s k) x)
    (hinj : ∀ k, InjOn f (s k))
    (g : E → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x in ⋃ k, s k, ENNReal.ofReal |(f' x).det| * g (f x) ∂μ) =
      ∫⁻ y, ((f ⁻¹' {y} ∩ ⋃ k, s k).encard : ℝ≥0∞) * g y ∂μ := by
  rw [countable_local_area_formula μ f f' s hs hd hf' hinj g hg]
  congr 1
  funext y
  exact countableChart_imageIndicators_eq_fiberCount f s hd hinj g y

#print axioms countableChart_imageIndicators_eq_fiberCount
#print axioms countable_local_area_formula_fiber_count
end SpectralRadiusUpperTail
