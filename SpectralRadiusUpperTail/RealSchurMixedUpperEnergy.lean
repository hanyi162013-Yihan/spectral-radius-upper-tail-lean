import SpectralRadiusUpperTail.RealSchurMixedUpperEntryCoordinates
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix BigOperators

theorem realSchurMixedDiagonalEnergy_join
    {m : ℕ} (s : Fin m → ℕ)
    (d : RealSchurMixedDiagonalEntry s → ℝ)
    (u : RealSchurMixedStrictUpperEntry s → ℝ) :
    realSchurMixedDiagonalEnergy s
      (realSchurMixedUpperEntryJoin s d u) =
        ∑ p : RealSchurMixedDiagonalEntry s, (d p)^2 := by
  classical
  let P : RealSchurMixedCoord s × RealSchurMixedCoord s → Prop :=
    fun p => p.1.1 = p.2.1
  have hp (p : RealSchurMixedCoord s × RealSchurMixedCoord s) :
      (if P p then (realSchurMixedUpperEntryJoin s d u p.1 p.2)^2 else 0) =
        if h : P p then (d ⟨p,h⟩)^2 else 0 := by
    by_cases h : P p <;> simp [P, realSchurMixedUpperEntryJoin, h]
  unfold realSchurMixedDiagonalEnergy
  change (∑ p, if P p then
    (realSchurMixedUpperEntryJoin s d u p.1 p.2)^2 else 0) = _
  simp_rw [hp]
  let f : RealSchurMixedCoord s × RealSchurMixedCoord s → ℝ :=
    fun p => if h : P p then (d ⟨p,h⟩)^2 else 0
  have hsum := Finset.sum_subtype_eq_sum_filter
    (s := Finset.univ)
    (f := f) (p := P)
  calc
    (∑ p, f p) = ∑ p, if P p then f p else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases h : P p <;> simp [f, h]
    _ = ∑ q ∈ Finset.subtype P Finset.univ, f q.val := by
      simpa only [Finset.sum_filter] using hsum.symm
    _ = ∑ q : RealSchurMixedDiagonalEntry s, (d q)^2 := by
      simp only [Finset.subtype_univ]
      apply Finset.sum_congr rfl
      intro q _
      simp [f, q.property]

theorem realSchurMixedStrictUpperEnergy_join
    {m : ℕ} (s : Fin m → ℕ)
    (d : RealSchurMixedDiagonalEntry s → ℝ)
    (u : RealSchurMixedStrictUpperEntry s → ℝ) :
    realSchurMixedStrictUpperEnergy s
      (realSchurMixedUpperEntryJoin s d u) =
        ∑ p : RealSchurMixedStrictUpperEntry s, (u p)^2 := by
  classical
  let P : RealSchurMixedCoord s × RealSchurMixedCoord s → Prop :=
    fun p => p.1.1 < p.2.1
  have hp (p : RealSchurMixedCoord s × RealSchurMixedCoord s) :
      (if P p then (realSchurMixedUpperEntryJoin s d u p.1 p.2)^2 else 0) =
        if h : P p then (u ⟨p,h⟩)^2 else 0 := by
    by_cases h : P p
    · have hn : p.1.1 ≠ p.2.1 := ne_of_lt h
      simp [P, realSchurMixedUpperEntryJoin, h, hn]
    · simp [P, h]
  unfold realSchurMixedStrictUpperEnergy
  change (∑ p, if P p then
    (realSchurMixedUpperEntryJoin s d u p.1 p.2)^2 else 0) = _
  simp_rw [hp]
  let f : RealSchurMixedCoord s × RealSchurMixedCoord s → ℝ :=
    fun p => if h : P p then (u ⟨p,h⟩)^2 else 0
  have hsum := Finset.sum_subtype_eq_sum_filter
    (s := Finset.univ)
    (f := f) (p := P)
  calc
    (∑ p, f p) = ∑ p, if P p then f p else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases h : P p <;> simp [f, h]
    _ = ∑ q ∈ Finset.subtype P Finset.univ, f q.val := by
      simpa only [Finset.sum_filter] using hsum.symm
    _ = ∑ q : RealSchurMixedStrictUpperEntry s, (u q)^2 := by
      simp only [Finset.subtype_univ]
      apply Finset.sum_congr rfl
      intro q _
      simp [f, q.property]

/-- In independent upper-entry coordinates, the Gaussian weight is a
product of the diagonal-block Gaussian and the strict-upper Gaussian. -/
theorem realSchurMixedGaussianWeight_join
    {m : ℕ} (s : Fin m → ℕ)
    (d : RealSchurMixedDiagonalEntry s → ℝ)
    (u : RealSchurMixedStrictUpperEntry s → ℝ) :
    realMatrixGaussianWeight (RealSchurMixedCoord s)
      (realSchurMixedUpperEntryJoin s d u) =
        Real.exp (-(∑ p : RealSchurMixedDiagonalEntry s, (d p)^2)/2) *
          Real.exp (-(∑ p : RealSchurMixedStrictUpperEntry s, (u p)^2)/2) := by
  rw [realSchurMixedGaussianWeight_factor s _
    (realSchurMixedUpperEntryJoin_lower_zero s d u),
    realSchurMixedDiagonalEnergy_join,
    realSchurMixedStrictUpperEnergy_join]

#print axioms realSchurMixedDiagonalEnergy_join
#print axioms realSchurMixedStrictUpperEnergy_join
#print axioms realSchurMixedGaussianWeight_join
end SpectralRadiusUpperTail
