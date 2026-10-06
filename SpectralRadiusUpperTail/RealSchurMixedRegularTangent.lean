import SpectralRadiusUpperTail.RealSchurMixedFullTangent
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- The actual lower angular derivative is invertible whenever its
determinant is nonzero, without choosing canonical block representatives. -/
noncomputable def realSchurMixedAngularEquivOfDet
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hdet : (realSchurMixedOrbitMatrix s T).det ≠ 0) :
    (RealSchurMixedOrbitIndex s → ℝ) ≃L[ℝ]
      (RealSchurMixedOrbitIndex s → ℝ) := by
  classical
  let M := realSchurMixedOrbitMatrix s T
  letI : Invertible M :=
    Matrix.invertibleOfIsUnitDet M (isUnit_iff_ne_zero.mpr hdet)
  exact (Matrix.toLinearEquiv' M inferInstance).toContinuousLinearEquiv

theorem realSchurMixedAngularEquivOfDet_apply
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hdet : (realSchurMixedOrbitMatrix s T).det ≠ 0)
    (ω : RealSchurMixedOrbitIndex s → ℝ) :
    realSchurMixedAngularEquivOfDet s T hdet ω =
      (realSchurMixedOrbitMatrix s T).mulVec ω := by
  classical
  unfold realSchurMixedAngularEquivOfDet
  change (Matrix.toLin' (realSchurMixedOrbitMatrix s T)) ω = _
  exact Matrix.toLin'_apply _ _

/-- The full mixed-Schur tangent is bijective at any matrix with a
nonsingular lower angular derivative. -/
theorem realSchurMixedTangentMap_bijective_of_orbit_det_ne_zero
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hdet : (realSchurMixedOrbitMatrix s T).det ≠ 0) :
    Function.Bijective (realSchurMixedTangentMap s T) := by
  let J := realSchurMixedAngularEquivOfDet s T hdet
  constructor
  · rintro ⟨ω,D⟩ ⟨η,E⟩ h
    have hl := congrArg (realSchurMixedLowerProjection s) h
    rw [realSchurMixedTangentMap_lower,
      realSchurMixedTangentMap_lower] at hl
    have hω : ω = η := J.injective (by
      rw [realSchurMixedAngularEquivOfDet_apply,
        realSchurMixedAngularEquivOfDet_apply]
      exact hl)
    apply Prod.ext hω
    apply Subtype.ext
    change D.val + (realSchurMixedSkewEmbed s ω*T -
      T*realSchurMixedSkewEmbed s ω) =
        E.val + (realSchurMixedSkewEmbed s η*T -
          T*realSchurMixedSkewEmbed s η) at h
    rw [hω] at h
    exact add_right_cancel h
  · intro A
    let ω : RealSchurMixedOrbitIndex s → ℝ :=
      J.symm (realSchurMixedLowerProjection s A)
    let C := realSchurMixedSkewEmbed s ω*T - T*realSchurMixedSkewEmbed s ω
    have hC : realSchurMixedLowerProjection s C =
        realSchurMixedLowerProjection s A := by
      calc
        realSchurMixedLowerProjection s C =
            (realSchurMixedOrbitMatrix s T).mulVec ω := by
          funext p
          exact realSchurMixedSkewEmbed_lower_action s T ω p
        _ = J ω := (realSchurMixedAngularEquivOfDet_apply s T hdet ω).symm
        _ = realSchurMixedLowerProjection s A := J.apply_symm_apply _
    have hD : A-C ∈ realSchurMixedUpperSubmodule s := by
      change realSchurMixedLowerProjection s (A-C) = 0
      rw [map_sub, hC, sub_self]
    refine ⟨(ω,⟨A-C,hD⟩), ?_⟩
    change A-C+C=A
    exact sub_add_cancel A C

/-- A regular mixed-Schur center has a continuous linear tangent inverse
with no canonical shape restriction on its diagonal blocks. -/
noncomputable def realSchurMixedTangentEquivOfDet
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hdet : (realSchurMixedOrbitMatrix s T).det ≠ 0) :
    RealSchurMixedTangent s ≃L[ℝ]
      Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ :=
  (LinearEquiv.ofBijective (realSchurMixedTangentMap s T)
    (realSchurMixedTangentMap_bijective_of_orbit_det_ne_zero s T hdet)).toContinuousLinearEquiv

#print axioms realSchurMixedTangentEquivOfDet
end SpectralRadiusUpperTail
