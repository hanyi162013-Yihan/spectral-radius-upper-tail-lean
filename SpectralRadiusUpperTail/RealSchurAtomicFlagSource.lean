import SpectralRadiusUpperTail.RealSchurAtomicCodeClass
import SpectralRadiusUpperTail.RealSchurMixedFlagFullFiber
import SpectralRadiusUpperTail.RealSchurMixedCodeClassFiber

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

noncomputable def realSchurAtomicFlagSource
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k : ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    Set (RealSchurMixedTangent s) :=
  realSchurMixedFlagCodedSource s hs c hc R k code ∩
    {x | realSchurAtomicCodeTest s code x.2.val}

noncomputable def realSchurAtomicDiagonalSource
    {m : ℕ} (s : Fin m → ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    Set (RealSchurMixedDiagonalEntry s → ℝ) :=
  realSchurMixedDiagonalCodeSource s code ∩
    {d | realSchurAtomicCodeTest s code (realSchurMixedUpperEntryJoin s d 0)}

theorem measurableSet_realSchurAtomicFlagSource
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k : ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    MeasurableSet (realSchurAtomicFlagSource s hs c hc R k code) :=
  (measurableSet_realSchurMixedFlagCodedSource s hs c hc R k code).inter
    ((measurableSet_realSchurAtomicCodeTest s code).preimage
      (continuous_subtype_val.comp continuous_snd).measurable)

theorem measurableSet_realSchurAtomicDiagonalSource
    {m : ℕ} (s : Fin m → ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    MeasurableSet (realSchurAtomicDiagonalSource s code) :=
  (measurableSet_realSchurMixedDiagonalCodeSource s code).inter
    ((measurableSet_realSchurAtomicCodeTest s code).preimage
      ((realSchurMixedUpperEntryJoin_continuous s).comp
        (continuous_id.prodMk continuous_const)).measurable)

/-- Restricting to genuine nonreal pairs leaves the complete angular
and strictly-upper fiber over each admissible diagonal array. -/
theorem realSchurAtomicFlagSource_full_fiber
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k : ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool)
    (w : RealSchurMixedOrbitIndex s → ℝ) (d : RealSchurMixedDiagonalEntry s → ℝ)
    (u : RealSchurMixedStrictUpperEntry s → ℝ) :
    realSchurMixedFiberPoint s w d u ∈ realSchurAtomicFlagSource s hs c hc R k code ↔
      w ∈ realSchurMixedFlagAnglePatch s hs c hc R k ∧ d ∈ realSchurAtomicDiagonalSource s code := by
  change (realSchurMixedFiberPoint s w d u ∈ realSchurMixedFlagCodedSource s hs c hc R k code ∧
    realSchurAtomicCodeTest s code (realSchurMixedUpperEntryJoin s d u)) ↔
      w ∈ realSchurMixedFlagAnglePatch s hs c hc R k ∧
        d ∈ realSchurMixedDiagonalCodeSource s code ∧
          realSchurAtomicCodeTest s code (realSchurMixedUpperEntryJoin s d 0)
  rw [realSchurMixedFlagCodedSource_full_fiber s hs c hc R k code w d u]
  have hpoly := realSchurMixedUpperEntryJoin_charpoly_fiber_const s hs d u 0
  by_cases hsep : (realSchurMixedUpperEntryJoin s d 0).charpoly.Separable
  · rw [realSchurAtomicCodeTest_iff_of_charpoly s code _ _ (hpoly.symm ▸ hsep) hsep hpoly]
    tauto
  · have hd : d ∉ realSchurMixedDiagonalCodeSource s code := fun h => hsep h.1
    simp only [hd,and_false,false_and]

#print axioms measurableSet_realSchurAtomicFlagSource
#print axioms measurableSet_realSchurAtomicDiagonalSource
#print axioms realSchurAtomicFlagSource_full_fiber
end SpectralRadiusUpperTail
