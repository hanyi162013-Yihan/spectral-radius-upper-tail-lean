import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal BigOperators

/-- The finite number of cover sets containing a point, viewed in the
nonnegative extended reals so that it can normalize area integrals. -/
noncomputable def finiteCoverMultiplicity
    {ι X : Type*} [Fintype ι] (S : ι → Set X) (x : X) : ℝ≥0∞ :=
  ∑ i, (S i).indicator (fun _ => (1 : ℝ≥0∞)) x

theorem finiteCoverMultiplicity_ne_top
    {ι X : Type*} [Fintype ι] (S : ι → Set X) (x : X) :
    finiteCoverMultiplicity S x ≠ ∞ := by
  classical
  apply ENNReal.sum_ne_top.mpr
  intro i _
  by_cases hx : x ∈ S i <;> simp [hx]

theorem finiteCoverMultiplicity_pos
    {ι X : Type*} [Fintype ι] (S : ι → Set X) (x : X)
    (hx : x ∈ ⋃ i, S i) : 0 < finiteCoverMultiplicity S x := by
  classical
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
  have hle : (1 : ℝ≥0∞) ≤ finiteCoverMultiplicity S x := by
    have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
      bot_le : ∀ j ∈ Finset.univ, (0 : ℝ≥0∞) ≤ (S j).indicator (fun _ => 1) x)
      (Finset.mem_univ i)
    simpa only [finiteCoverMultiplicity, Set.indicator_of_mem hi] using h
  exact lt_of_lt_of_le zero_lt_one hle

theorem finiteCoverMultiplicity_measurable
    {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (S : ι → Set X) (hS : ∀ i, MeasurableSet (S i)) :
    Measurable (finiteCoverMultiplicity S) := by
  classical
  unfold finiteCoverMultiplicity
  exact Finset.measurable_sum Finset.univ (fun i _ => measurable_const.indicator (hS i))

/-- Weighting each occurrence by the reciprocal of its finite cover
multiplicity counts every covered point exactly once. -/
theorem finiteCover_normalized_indicator_sum
    {ι X : Type*} [Fintype ι] (S : ι → Set X) (f : X → ℝ≥0∞) (x : X) :
    (∑ i, (S i).indicator (fun y => (finiteCoverMultiplicity S y)⁻¹*f y) x) =
      (⋃ i, S i).indicator f x := by
  classical
  have hsum : (∑ i, (S i).indicator (fun y => (finiteCoverMultiplicity S y)⁻¹*f y) x) =
      finiteCoverMultiplicity S x * ((finiteCoverMultiplicity S x)⁻¹*f x) := by
    change _ = (∑ i, (S i).indicator (fun _ => (1 : ℝ≥0∞)) x) *
      ((finiteCoverMultiplicity S x)⁻¹*f x)
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : x ∈ S i <;> simp [hi]
  rw [hsum, ← mul_assoc]
  by_cases hx : x ∈ ⋃ i, S i
  · rw [ENNReal.mul_inv_cancel (ne_of_gt (finiteCoverMultiplicity_pos S x hx))
      (finiteCoverMultiplicity_ne_top S x), one_mul, Set.indicator_of_mem hx]
  · have hzero : finiteCoverMultiplicity S x=0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact Set.indicator_of_notMem (fun hi => hx (Set.mem_iUnion_of_mem i hi)) _
    rw [hzero,zero_mul,zero_mul,Set.indicator_of_notMem hx]

/-- An exact integral identity for finite measurable covers with
overlaps. No disjointness or constant global multiplicity is assumed. -/
theorem lintegral_finiteCover_normalized
    {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (S : ι → Set X) (hS : ∀ i, MeasurableSet (S i))
    (μ : Measure X) (f : X → ℝ≥0∞) (hf : Measurable f) :
    (∑ i, ∫⁻ x in S i, (finiteCoverMultiplicity S x)⁻¹*f x ∂μ) =
      ∫⁻ x in ⋃ i, S i, f x ∂μ := by
  classical
  have hg : Measurable (fun x => (finiteCoverMultiplicity S x)⁻¹*f x) :=
    (finiteCoverMultiplicity_measurable S hS).inv.mul hf
  simp_rw [← lintegral_indicator (hS _)]
  rw [← lintegral_finsetSum Finset.univ (fun i _ => hg.indicator (hS i))]
  simp_rw [finiteCover_normalized_indicator_sum]
  exact lintegral_indicator (MeasurableSet.iUnion hS) f

#print axioms finiteCoverMultiplicity_ne_top
#print axioms finiteCoverMultiplicity_pos
#print axioms finiteCoverMultiplicity_measurable
#print axioms finiteCover_normalized_indicator_sum
#print axioms lintegral_finiteCover_normalized
end SpectralRadiusUpperTail
