import SpectralRadiusUpperTail.RealSchurMixedEntryEquiv
import Ginibre.BlockLinearDeterminant
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- Block-upper variables translate without an angular contribution when
the angular parameter is zero. -/
theorem realSchurMixedTangentMap_upper
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (D : realSchurMixedUpperSubmodule s) :
    realSchurMixedTangentMap s T (0,D) = D.val := by
  have hz : realSchurMixedSkewEmbed s
      (0 : RealSchurMixedOrbitIndex s → ℝ) = 0 :=
    (realSchurMixedSkewCLM s).map_zero
  change D.val + (realSchurMixedSkewEmbed s 0*T -
    T*realSchurMixedSkewEmbed s 0) = D.val
  rw [hz, Matrix.zero_mul, Matrix.mul_zero, sub_self, add_zero]

/-- Express the full genuine Schur tangent map in fixed matrix-entry
coordinates. -/
noncomputable def realSchurMixedCoordinateDifferential
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    RealSchurMixedTangent s →ₗ[ℝ] RealSchurMixedTangent s :=
  (realSchurMixedEntryEquiv s).toLinearMap.comp
    (realSchurMixedTangentMap s T)

/-- The complete center Jacobian has exactly the angular determinant;
the remaining block-upper coordinates contribute an identity block. -/
theorem realSchurMixedCoordinateDifferential_det
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    LinearMap.det (realSchurMixedCoordinateDifferential s T) =
      (realSchurMixedOrbitMatrix s T).det := by
  have hd : LinearMap.det (realSchurMixedCoordinateDifferential s T) =
      LinearMap.det (Matrix.toLin' (realSchurMixedOrbitMatrix s T)) := by
    apply Ginibre.det_block_lower_identity
    · intro x
      funext p
      exact congrFun (realSchurMixedTangentMap_lower s T x) p
    · intro D
      change realSchurMixedUpperEntries s
        (realSchurMixedTangentMap s T (0,D)) = D
      rw [realSchurMixedTangentMap_upper,
        realSchurMixedUpperEntries_upper]
  rw [hd, LinearMap.det_toLin']

/-- For mixed 1×1/2×2 diagonal patterns, the absolute determinant of the
full Schur tangent is the complete product of spectral gaps. -/
theorem realSchurMixedCoordinateDifferential_abs_det
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b) :
    |LinearMap.det (realSchurMixedCoordinateDifferential
      (fun i => (B i).size) T)| =
        ∏ p : RealSchurLowerIndex m,
          realSchurSpectralGap (B p.1.1).data (B p.1.2).data := by
  rw [realSchurMixedCoordinateDifferential_det]
  exact realSchurChartBlock_orbit_abs_det B T hT hdiag

#print axioms realSchurMixedCoordinateDifferential_det
#print axioms realSchurMixedCoordinateDifferential_abs_det
end SpectralRadiusUpperTail
