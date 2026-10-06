import SpectralRadiusUpperTail.MarkedRealAngularProductInjective
import SpectralRadiusUpperTail.RealSchurMixedChartSpectrum
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Set
open scoped Matrix

/-- A fixed angular branch with a positive-oriented first column. It
does not depend on the Schur scalar, complementary block, or upper row. -/
def markedRealAngularPositiveSource (m : ℕ) :
    Set (RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ) :=
  (realSchurMixedAngularProjectionChart
    (markedRealTwoBlockSizes m)).source ∩
    {w | 0 < (realSchurMixedAngularFrame (markedRealTwoBlockSizes m) w)
      (markedRealFirstCoordinate m) (markedRealFirstCoordinate m)}

/-- The complementary product factor imposes simple spectrum and a
scalar cutoff, but places no restriction on the angular coordinate. -/
def markedRealUpperSimpleSource (m : ℕ) (b : ℝ) :
    Set (realSchurMixedUpperSubmodule (markedRealTwoBlockSizes m)) :=
  {S | S.val.charpoly.Separable ∧ b < markedRealScalar m S.val}

/-- The complete marked-root map on the independent angular/upper
product coordinates. -/
noncomputable def markedRealAngularProductMap (m : ℕ) :
    ((RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ) ×
      realSchurMixedUpperSubmodule (markedRealTwoBlockSizes m)) →
      (Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
        (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ × ℝ) :=
  fun p =>
    let Q := realSchurMixedAngularFrame (markedRealTwoBlockSizes m) p.1
    (Q*p.2.val*Qᵀ, markedRealScalar m p.2.val)

/-- On the product of a fixed angular branch and all simple block-upper
matrices, each marked matrix-root pair has a unique parameter. -/
theorem markedRealAngularProductMap_injOn
    (m : ℕ) (b : ℝ) :
    InjOn (markedRealAngularProductMap m)
      (markedRealAngularPositiveSource m ×ˢ
        markedRealUpperSimpleSource m b) := by
  intro p hp q hq heq
  rcases p with ⟨w,S⟩
  rcases q with ⟨v,T⟩
  have hw := hp.1.1
  have hv := hq.1.1
  have hwpos := hp.1.2
  have hvpos := hq.1.2
  have hsepS := hp.2.1
  have hscalar : markedRealScalar m S.val = markedRealScalar m T.val :=
    congrArg Prod.snd heq
  have hmat :
      (realSchurMixedAngularFrame (markedRealTwoBlockSizes m) w) * S.val *
        (realSchurMixedAngularFrame (markedRealTwoBlockSizes m) w)ᵀ =
      (realSchurMixedAngularFrame (markedRealTwoBlockSizes m) v) * T.val *
        (realSchurMixedAngularFrame (markedRealTwoBlockSizes m) v)ᵀ :=
    congrArg Prod.fst heq
  have hsep : ((realSchurMixedAngularFrame
      (markedRealTwoBlockSizes m) w) * S.val *
      (realSchurMixedAngularFrame (markedRealTwoBlockSizes m) w)ᵀ).charpoly.Separable := by
    rw [realMatrixOrthogonalConjugation_charpoly _ _ _
      (realSchurMixedAngularFrame_orthogonal _ w)]
    exact hsepS
  obtain ⟨hwv,hST⟩ := markedRealAngular_upperProduct_injective_at_root
    m w v S.val T.val hw hv hwpos hvpos S.property T.property
      hscalar hmat hsep
  exact Prod.ext hwv (Subtype.ext hST)

#print axioms markedRealAngularProductMap_injOn
end SpectralRadiusUpperTail
