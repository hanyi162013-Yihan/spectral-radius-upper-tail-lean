import SpectralRadiusUpperTail.RealSchurMixedBlockGap
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

theorem RealSchurChartBlock.data_admissible (B : RealSchurChartBlock) :
    realSchurDataAdmissible B.data := by
  cases B with
  | scalar a => trivial
  | pair x b c y hbc hy => exact hy

/-- Distinct admissible diagonal spectral blocks make the mixed-size
angular Jacobian nonzero. This is the regularity needed for a local real
Schur chart, before a global atlas is constructed. -/
theorem realSchurChartBlock_orbit_det_ne_zero
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (hsep : ∀ p : RealSchurLowerIndex m,
      realSchurDataSeparated (B p.1.1).data (B p.1.2).data) :
    (realSchurMixedOrbitMatrix (fun i => (B i).size) T).det ≠ 0 := by
  have hprod : 0 < ∏ p : RealSchurLowerIndex m,
      realSchurSpectralGap (B p.1.1).data (B p.1.2).data := by
    apply Finset.prod_pos
    intro p _
    exact realSchurSpectralGap_pos _ _
      (B p.1.1).data_admissible (B p.1.2).data_admissible (hsep p)
  rw [← realSchurChartBlock_orbit_abs_det B T hT hdiag] at hprod
  exact (abs_pos.mp hprod)

#print axioms realSchurChartBlock_orbit_det_ne_zero
end SpectralRadiusUpperTail
