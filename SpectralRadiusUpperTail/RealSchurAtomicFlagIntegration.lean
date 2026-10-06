import SpectralRadiusUpperTail.RealSchurAtomicFlagImage
import SpectralRadiusUpperTail.RealSchurMixedFlagCodedIntegration

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

theorem realSchurAtomicFlagSource_injOn
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k : ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    Set.InjOn (realSchurMixedRotatedEntryCoordinates s 0 (R k).val (R k).property)
      (realSchurAtomicFlagSource s hs c hc R k code) := by
  exact (realSchurMixedFlagCodedSource_injOn s hs c hc R k code).mono
    Set.inter_subset_left

theorem measurableSet_realSchurAtomicFlagImage
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s) (k : ℕ)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    MeasurableSet (realSchurMixedRotatedEntryCoordinates s 0 (R k).val (R k).property ''
      realSchurAtomicFlagSource s hs c hc R k code) := by
  exact measurable_image_of_fderivWithin
    (measurableSet_realSchurAtomicFlagSource s hs c hc R k code)
    (fun x _ => (realSchurMixedRotatedEntryCoordinates_differentiable s 0
      (R k).val (R k).property x).hasFDerivAt.hasFDerivWithinAt)
    (realSchurAtomicFlagSource_injOn s hs c hc R k code)

theorem pairwise_realSchurAtomicFlagImage
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s)
    (code : Fin m → Fin (Fintype.card (RealSchurMixedCoord s)) → Bool) :
    Pairwise (fun k l => Disjoint
      (realSchurMixedRotatedEntryCoordinates s 0 (R k).val (R k).property ''
        realSchurAtomicFlagSource s hs c hc R k code)
      (realSchurMixedRotatedEntryCoordinates s 0 (R l).val (R l).property ''
        realSchurAtomicFlagSource s hs c hc R l code)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
  exact hkl (realSchurMixedFlagCodedSource_unique s hs c hc R k l code x y hx.1 hy.1
    (hxz.trans hyz.symm)).1

#print axioms realSchurAtomicFlagSource_injOn
#print axioms measurableSet_realSchurAtomicFlagImage
#print axioms pairwise_realSchurAtomicFlagImage
end SpectralRadiusUpperTail
