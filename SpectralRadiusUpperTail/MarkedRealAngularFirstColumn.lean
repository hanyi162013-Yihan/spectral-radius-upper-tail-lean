import SpectralRadiusUpperTail.RealSchurMixedAngularProjectionChart
import SpectralRadiusUpperTail.MarkedRealTwoBlockOrbit
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- In the `(1,m)` shape, the independent angular projection really is
the complementary part of the orthogonal frame's first column. -/
theorem markedRealAngularProjection_apply
    (m : ℕ)
    (w : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ)
    (i : Fin m) :
    realSchurMixedAngularProjection (markedRealTwoBlockSizes m) w
        (markedRealOrbitEquiv m i) =
      -(realSchurMixedAngularFrame (markedRealTwoBlockSizes m) w)
        ⟨1,i⟩ ⟨0,markedRealZeroCoordinate m⟩ := by
  rfl

/-- On the inverse-function chart, an angular parameter is determined
by the first column of its orthogonal frame. The domain is independent
of the scalar eigenvalue, complementary block, and free upper row. -/
theorem markedRealAngularFrame_firstColumn_injOn
    (m : ℕ)
    (w v : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ)
    (hw : w ∈ (realSchurMixedAngularProjectionChart
      (markedRealTwoBlockSizes m)).source)
    (hv : v ∈ (realSchurMixedAngularProjectionChart
      (markedRealTwoBlockSizes m)).source)
    (hcol : ∀ i : Fin m,
      (realSchurMixedAngularFrame (markedRealTwoBlockSizes m) w)
        ⟨1,i⟩ ⟨0,markedRealZeroCoordinate m⟩ =
      (realSchurMixedAngularFrame (markedRealTwoBlockSizes m) v)
        ⟨1,i⟩ ⟨0,markedRealZeroCoordinate m⟩) :
    w = v := by
  have hproj : realSchurMixedAngularProjection (markedRealTwoBlockSizes m) w =
      realSchurMixedAngularProjection (markedRealTwoBlockSizes m) v := by
    funext q
    let i := (markedRealOrbitEquiv m).symm q
    have hq : markedRealOrbitEquiv m i = q := Equiv.apply_symm_apply _ _
    rw [← hq, markedRealAngularProjection_apply,
      markedRealAngularProjection_apply, hcol i]
  exact (realSchurMixedAngularProjectionChart
    (markedRealTwoBlockSizes m)).injOn hw hv hproj

#print axioms markedRealAngularProjection_apply
#print axioms markedRealAngularFrame_firstColumn_injOn
end SpectralRadiusUpperTail
