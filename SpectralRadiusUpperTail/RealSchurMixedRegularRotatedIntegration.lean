import SpectralRadiusUpperTail.RealSchurMixedRegularIntegration
import SpectralRadiusUpperTail.RealSchurMixedOutputCoordinateVolume
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped ENNReal Matrix Matrix.Norms.Operator

/-- The actual chart output, in fixed lower/upper entry coordinates,
after rotating by an arbitrary orthogonal frame. -/
noncomputable def realSchurMixedRotatedEntryCoordinates
    {m : ℕ} (s : Fin m → ℕ)
    (T Q : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hQ : Qᵀ*Q=1) (x : RealSchurMixedTangent s) :
    RealSchurMixedTangent s :=
  realSchurMixedOutputCoordinateEquiv s Q hQ
    (realSchurMixedEntryCoordinates s T x)

/-- Rotation of a regular chart has the same explicit local Jacobian;
the output orthogonal conjugation preserves the matrix-entry volume. -/
theorem realSchurMixed_lintegral_regular_rotated_chart
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T Q : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T = 0)
    (hdet : (realSchurMixedOrbitMatrix s T).det ≠ 0)
    (hQ : Qᵀ*Q=1)
    (U : Set (RealSchurMixedTangent s))
    (hU : MeasurableSet U)
    (hsub : U ⊆ (realSchurMixedRegularChart s T hdet).source)
    (g : RealSchurMixedTangent s → ℝ≥0∞) :
    ∫⁻ y in realSchurMixedRotatedEntryCoordinates s T Q hQ '' U,
        g y ∂realSchurMixedCoordinateVolume s =
      ∫⁻ x in U,
        ENNReal.ofReal (realSchurMixedJacobianWeight s T x) *
          g (realSchurMixedRotatedEntryCoordinates s T Q hQ x)
        ∂realSchurMixedCoordinateVolume s := by
  let E := realSchurMixedOutputCoordinateEquiv s Q hQ
  have hE := realSchurMixedOutputCoordinateEquiv_measurePreserving s Q hQ
  have hEmb : MeasurableEmbedding E :=
    E.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have h := hE.setLIntegral_comp_emb hEmb g
    (realSchurMixedEntryCoordinates s T '' U)
  have hreg := realSchurMixed_lintegral_regular_chart s hs T hT hdet U hU hsub
    (fun y => g (E y))
  rw [hreg] at h
  change (∫⁻ y in (fun x => E (realSchurMixedEntryCoordinates s T x)) '' U,
      g y ∂realSchurMixedCoordinateVolume s) =
    ∫⁻ x in U,
      ENNReal.ofReal (realSchurMixedJacobianWeight s T x) *
        g (E (realSchurMixedEntryCoordinates s T x))
      ∂realSchurMixedCoordinateVolume s
  simpa only [Set.image_image, Function.comp_def] using h.symm

#print axioms realSchurMixed_lintegral_regular_rotated_chart
end SpectralRadiusUpperTail
