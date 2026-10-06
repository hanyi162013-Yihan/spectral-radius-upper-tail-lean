import SpectralRadiusUpperTail.RealSchurMixedFlagCodedSource
import SpectralRadiusUpperTail.RealSchurMixedSpectralFiber

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

noncomputable def realSchurMixedDiagonalCodeSource
    {m : ℕ} (s : Fin m → ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    Set (RealSchurMixedDiagonalEntry s → ℝ) :=
  {d | (realSchurMixedUpperEntryJoin s d 0).charpoly.Separable ∧
    realSchurMixedSpectralCode s (realSchurMixedUpperEntryJoin s d 0)=code}

theorem measurableSet_realSchurMixedDiagonalCodeSource
    {m : ℕ} (s : Fin m → ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    MeasurableSet (realSchurMixedDiagonalCodeSource s code) := by
  have hjoin : Continuous (fun d : RealSchurMixedDiagonalEntry s → ℝ =>
      realSchurMixedUpperEntryJoin s d 0) := by
    apply continuous_matrix
    intro i j
    unfold realSchurMixedUpperEntryJoin
    split_ifs <;> fun_prop
  exact ((isOpen_realMatrix_charpoly_separable _).preimage hjoin).measurableSet.inter
    (measurableSet_eq_fun ((realSchurMixedSpectralCode_measurable s).comp hjoin.measurable)
      measurable_const)

/-- The coded angle source is exactly a product of an angular patch,
a diagonal spectral class, and the entire strict-upper entry space.
This removes the truncation that occurs for ordinary local Schur charts. -/
theorem realSchurMixedFlagCodedSource_full_fiber
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k : ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (w : RealSchurMixedOrbitIndex s → ℝ)
    (d : RealSchurMixedDiagonalEntry s → ℝ)
    (u : RealSchurMixedStrictUpperEntry s → ℝ) :
    realSchurMixedFiberPoint s w d u ∈ realSchurMixedFlagCodedSource s hs c hc R k code ↔
      w ∈ realSchurMixedFlagAnglePatch s hs c hc R k ∧
        d ∈ realSchurMixedDiagonalCodeSource s code := by
  change (w ∈ realSchurMixedFlagAnglePatch s hs c hc R k ∧
    (realSchurMixedUpperEntryJoin s d u).charpoly.Separable ∧
      realSchurMixedSpectralCode s (realSchurMixedUpperEntryJoin s d u)=code) ↔
    w ∈ realSchurMixedFlagAnglePatch s hs c hc R k ∧
      (realSchurMixedUpperEntryJoin s d 0).charpoly.Separable ∧
        realSchurMixedSpectralCode s (realSchurMixedUpperEntryJoin s d 0)=code
  have hpoly := realSchurMixedUpperEntryJoin_charpoly_fiber_const s hs d u 0
  rw [hpoly]
  by_cases hsep : (realSchurMixedUpperEntryJoin s d 0).charpoly.Separable
  · rw [realSchurMixedSpectralCode_fiber_const s hs d u 0 (hpoly.symm ▸ hsep)]
  · simp only [hsep, false_and, and_false]

#print axioms measurableSet_realSchurMixedDiagonalCodeSource
#print axioms realSchurMixedFlagCodedSource_full_fiber
end SpectralRadiusUpperTail
