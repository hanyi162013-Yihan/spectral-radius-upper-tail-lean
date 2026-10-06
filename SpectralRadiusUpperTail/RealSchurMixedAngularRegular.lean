import SpectralRadiusUpperTail.RealSchurMixedAngularDerivative
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator RightActions

/-- At separated admissible real Schur blocks, the derivative of the
orthogonal angular chart projected to lower-block entries is bijective. -/
theorem realSchurMixedAngularDerivative_bijective
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (hsep : ∀ p : RealSchurLowerIndex m,
      realSchurDataSeparated (B p.1.1).data (B p.1.2).data) :
    Function.Bijective
      ((realSchurMixedLowerProjection (fun i => (B i).size)).comp
        ((realSchurMixedSkewCLM (fun i => (B i).size) <• T) -
          T • realSchurMixedSkewCLM (fun i => (B i).size))) := by
  classical
  let s := fun i : Fin m => (B i).size
  let M := realSchurMixedOrbitMatrix s T
  have hdet : M.det ≠ 0 :=
    realSchurChartBlock_orbit_det_ne_zero B T hT hdiag hsep
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  letI : Invertible M := Matrix.invertibleOfIsUnitDet M hunit
  rw [realSchurMixedAngularDerivative_eq_matrix]
  exact (Matrix.toLinearEquiv' M inferInstance).bijective

#print axioms realSchurMixedAngularDerivative_bijective
end SpectralRadiusUpperTail
