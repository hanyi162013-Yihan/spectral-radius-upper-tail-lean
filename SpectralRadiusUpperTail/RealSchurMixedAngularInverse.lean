import SpectralRadiusUpperTail.RealSchurMixedAngularRegular
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator RightActions

/-- Separated block spectra make the lower angular derivative a continuous
linear equivalence. -/
noncomputable def realSchurMixedAngularDerivativeEquiv
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (hsep : ∀ p : RealSchurLowerIndex m,
      realSchurDataSeparated (B p.1.1).data (B p.1.2).data) :
    (RealSchurMixedOrbitIndex (fun i => (B i).size) → ℝ) ≃L[ℝ]
      (RealSchurMixedOrbitIndex (fun i => (B i).size) → ℝ) := by
  classical
  let s := fun i : Fin m => (B i).size
  let M := realSchurMixedOrbitMatrix s T
  have hdet : M.det ≠ 0 :=
    realSchurChartBlock_orbit_det_ne_zero B T hT hdiag hsep
  letI : Invertible M :=
    Matrix.invertibleOfIsUnitDet M (isUnit_iff_ne_zero.mpr hdet)
  exact (Matrix.toLinearEquiv' M inferInstance).toContinuousLinearEquiv

theorem realSchurMixedAngularDerivativeEquiv_apply
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (hsep : ∀ p : RealSchurLowerIndex m,
      realSchurDataSeparated (B p.1.1).data (B p.1.2).data)
    (ω : RealSchurMixedOrbitIndex (fun i => (B i).size) → ℝ) :
    realSchurMixedAngularDerivativeEquiv B T hT hdiag hsep ω =
      (realSchurMixedOrbitMatrix (fun i => (B i).size) T).mulVec ω := by
  classical
  unfold realSchurMixedAngularDerivativeEquiv
  change (Matrix.toLin'
    (realSchurMixedOrbitMatrix (fun i => (B i).size) T)) ω = _
  exact Matrix.toLin'_apply _ _

#print axioms realSchurMixedAngularDerivativeEquiv_apply
end SpectralRadiusUpperTail
