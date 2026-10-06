import SpectralRadiusUpperTail.RealSchurNativeCoordinateEmbedding
import SpectralRadiusUpperTail.RealSchurMixedUpperEntryCoordinates
import SpectralRadiusUpperTail.IndependentCoordinateSelection
import SpectralRadiusUpperTail.RealSchurGlobalModel

namespace SpectralRadiusUpperTail
open MeasureTheory

def realSchurNativeUpperEmbedding {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, s i ≤ 2) :
    RealSchurMixedStrictUpperEntry s ↪ SchurEntryIndex m 2 where
  toFun p := ((p.val.1.1,p.val.2.1),
    (Fin.castLE (hs p.val.1.1) p.val.1.2,Fin.castLE (hs p.val.2.1) p.val.2.2))
  inj' := by
    intro p q h
    apply Subtype.ext
    apply Prod.ext
    · apply (realSchurNativeCoordEmbedding s hs).injective
      exact Prod.ext (congrArg (fun v : SchurEntryIndex m 2 => v.1.1) h)
        (congrArg (fun v : SchurEntryIndex m 2 => v.2.1) h)
    · apply (realSchurNativeCoordEmbedding s hs).injective
      exact Prod.ext (congrArg (fun v : SchurEntryIndex m 2 => v.1.2) h)
        (congrArg (fun v : SchurEntryIndex m 2 => v.2.2) h)

def realSchurNativeUpperSelect {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, s i ≤ 2)
    (w : SchurEntryIndex m 2 → ℝ) : RealSchurMixedStrictUpperEntry s → ℝ :=
  fun p => w (realSchurNativeUpperEmbedding s hs p)

theorem realSchurNativeUpperSelect_measurePreserving {m : ℕ}
    (s : Fin m → ℕ) (hs : ∀ i, s i ≤ 2) :
    MeasurePreserving (realSchurNativeUpperSelect s hs)
      (Measure.pi (fun _ : SchurEntryIndex m 2 => standardNormal))
      (Measure.pi (fun _ : RealSchurMixedStrictUpperEntry s => standardNormal)) :=
  ⟨by unfold realSchurNativeUpperSelect; fun_prop,independent_coordinate_selection_law _
    (realSchurNativeUpperEmbedding s hs) (realSchurNativeUpperEmbedding s hs).injective⟩

#print axioms realSchurNativeUpperEmbedding
#print axioms realSchurNativeUpperSelect_measurePreserving
end SpectralRadiusUpperTail
