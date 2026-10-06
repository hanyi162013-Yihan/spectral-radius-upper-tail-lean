import SpectralRadiusUpperTail.RealSchurMixedExpCoordinates
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator RightActions

/-- Read all entries in the lower Schur blocks of a full real matrix. -/
noncomputable def realSchurMixedLowerProjection
    {m : ℕ} (s : Fin m → ℕ) :
    Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ →L[ℝ]
      (RealSchurMixedOrbitIndex s → ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A p => A ⟨p.1.1.1,p.2.1⟩ ⟨p.1.1.2,p.2.2⟩
    map_add' := by intro A B; rfl
    map_smul' := by intro a A; rfl }

/-- The linearized lower-entry projection of the genuine exponential
conjugation is exactly multiplication by the mixed angular Jacobian. -/
theorem realSchurMixedAngularDerivative_apply
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (ω : RealSchurMixedOrbitIndex s → ℝ) :
    (realSchurMixedLowerProjection s)
      (((realSchurMixedSkewCLM s <• T) - T • realSchurMixedSkewCLM s) ω) =
        (realSchurMixedOrbitMatrix s T).mulVec ω := by
  funext p
  change (realSchurMixedSkewEmbed s ω*T -
    T*realSchurMixedSkewEmbed s ω)
      ⟨p.1.1.1,p.2.1⟩ ⟨p.1.1.2,p.2.2⟩ = _
  exact realSchurMixedSkewEmbed_lower_action s T ω p

/-- The projected derivative, as a continuous linear operator, has the
concrete matrix already factored into spectral gaps. -/
theorem realSchurMixedAngularDerivative_eq_matrix
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    (realSchurMixedLowerProjection s).comp
      ((realSchurMixedSkewCLM s <• T) - T • realSchurMixedSkewCLM s) =
        LinearMap.toContinuousLinearMap
          (Matrix.toLin' (realSchurMixedOrbitMatrix s T)) := by
  ext ω p
  exact congrFun (realSchurMixedAngularDerivative_apply s T ω) p

#print axioms realSchurMixedAngularDerivative_apply
#print axioms realSchurMixedAngularDerivative_eq_matrix
end SpectralRadiusUpperTail
