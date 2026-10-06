import SpectralRadiusUpperTail.RealSchurMixedUpperEnergy
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator ContDiff Topology

theorem realSchurMixedEntryCoordinates_contDiff
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (k : ℕ∞ω) :
    ContDiff ℝ k (realSchurMixedEntryCoordinates s T) := by
  exact (realSchurMixedEntryEquiv s).toContinuousLinearEquiv.contDiff.comp
    (realSchurMixedExpCoordinates_contDiff s T k)

theorem realSchurMixedEntryCoordinates_det_continuous
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    Continuous (fun x : RealSchurMixedTangent s =>
      (fderiv ℝ (realSchurMixedEntryCoordinates s T) x).det) := by
  exact ContinuousLinearMap.continuous_det.comp
    ((realSchurMixedEntryCoordinates_contDiff s T 1).continuous_fderiv one_ne_zero)

theorem realSchurMixedAngularJacobian_eq_det_div
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T = 0)
    (hM : (realSchurMixedOrbitMatrix s T).det ≠ 0)
    (w : RealSchurMixedOrbitIndex s → ℝ) :
    realSchurMixedAngularJacobian s w =
      (fderiv ℝ (realSchurMixedEntryCoordinates s T)
        (w, (0 : realSchurMixedUpperSubmodule s))).det /
        (realSchurMixedOrbitMatrix s T).det := by
  have h := realSchurMixedEntryCoordinates_fderiv_det_everywhere s T hT
    (w, (0 : realSchurMixedUpperSubmodule s))
  simp only [Submodule.coe_zero, add_zero] at h
  apply (eq_div_iff hM).2
  simpa only [mul_comm] using h.symm

/-- The genuine angular Jacobian is continuous wherever one regular
mixed-block Schur center is available. -/
theorem realSchurMixedAngularJacobian_continuous
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T = 0)
    (hM : (realSchurMixedOrbitMatrix s T).det ≠ 0) :
    Continuous (realSchurMixedAngularJacobian s) := by
  have hc : Continuous (fun w : RealSchurMixedOrbitIndex s → ℝ =>
      (fderiv ℝ (realSchurMixedEntryCoordinates s T)
        (w, (0 : realSchurMixedUpperSubmodule s))).det /
          (realSchurMixedOrbitMatrix s T).det) :=
    ((realSchurMixedEntryCoordinates_det_continuous s T).comp
      (continuous_id.prodMk continuous_const)).div_const _
  exact hc.congr (fun w => (realSchurMixedAngularJacobian_eq_det_div s T hT hM w).symm)

/-- Near a separated mixed real-Schur center, the angular Jacobian
remains strictly positive and hence cannot cancel the spectral factors. -/
theorem realSchurMixedAngularJacobian_pos_nhds_zero
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (hsep : ∀ p : RealSchurLowerIndex m,
      realSchurDataSeparated (B p.1.1).data (B p.1.2).data) :
    {w : RealSchurMixedOrbitIndex (fun i => (B i).size) → ℝ |
      0 < realSchurMixedAngularJacobian (fun i => (B i).size) w} ∈ 𝓝 0 := by
  let s := fun i : Fin m => (B i).size
  have hupper : realSchurMixedLowerProjection s T = 0 := by
    apply (realSchurMixed_blockTriangular_iff_lower_zero s T).mp
    intro u v huv
    exact hT u.1 v.1 huv u.2 v.2
  have hM := realSchurChartBlock_orbit_det_ne_zero B T hT hdiag hsep
  have hc := realSchurMixedAngularJacobian_continuous s T hupper hM
  apply IsOpen.mem_nhds
  · exact isOpen_Ioi.preimage hc
  · simpa only [Set.mem_setOf_eq, realSchurMixedAngularJacobian_zero] using
      (show (0 : ℝ) < 1 by norm_num)

#print axioms realSchurMixedAngularJacobian_continuous
#print axioms realSchurMixedAngularJacobian_pos_nhds_zero
end SpectralRadiusUpperTail
