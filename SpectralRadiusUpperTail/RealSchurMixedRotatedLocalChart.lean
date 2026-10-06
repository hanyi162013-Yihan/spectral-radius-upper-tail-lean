import SpectralRadiusUpperTail.RealSchurMixedOrthogonalTransport
import SpectralRadiusUpperTail.RealSchurMixedFullChart
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- Rotate the genuine local real-Schur chart around an arbitrary
orthogonal Schur frame. -/
noncomputable def realSchurMixedRotatedLocalChart
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (hsep : ∀ p : RealSchurLowerIndex m,
      realSchurDataSeparated (B p.1.1).data (B p.1.2).data)
    (Q : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hQ : Qᵀ*Q=1) :
    OpenPartialHomeomorph
      (RealSchurMixedTangent (fun i => (B i).size))
      (Matrix (RealSchurMixedCoord (fun i => (B i).size))
        (RealSchurMixedCoord (fun i => (B i).size)) ℝ) :=
  (realSchurMixedLocalChart B T hT hdiag hsep).transHomeomorph
    (realMatrixOrthogonalConjugationEquiv _ Q hQ).toContinuousLinearEquiv.toHomeomorph

theorem realSchurMixedRotatedLocalChart_zero_mem_source
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (hsep : ∀ p : RealSchurLowerIndex m,
      realSchurDataSeparated (B p.1.1).data (B p.1.2).data)
    (Q : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hQ : Qᵀ*Q=1) :
    0 ∈ (realSchurMixedRotatedLocalChart B T hT hdiag hsep Q hQ).source := by
  exact realSchurMixedLocalChart_zero_mem_source B T hT hdiag hsep

/-- Every orthogonal conjugate of a separated block-upper center lies
in a genuine open local chart. -/
theorem realSchurMixedRotatedLocalChart_center_mem_target
    {m : ℕ} (B : Fin m → RealSchurChartBlock)
    (T : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hT : ∀ a b : Fin m, b < a →
      ∀ x : Fin ((B a).size), ∀ y : Fin ((B b).size),
        T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (hdiag : ∀ i a b, T ⟨i,a⟩ ⟨i,b⟩ = (B i).matrix a b)
    (hsep : ∀ p : RealSchurLowerIndex m,
      realSchurDataSeparated (B p.1.1).data (B p.1.2).data)
    (Q : Matrix (RealSchurMixedCoord (fun i => (B i).size))
      (RealSchurMixedCoord (fun i => (B i).size)) ℝ)
    (hQ : Qᵀ*Q=1) :
    Q*T*Qᵀ ∈
      (realSchurMixedRotatedLocalChart B T hT hdiag hsep Q hQ).target := by
  have h := (realSchurMixedRotatedLocalChart B T hT hdiag hsep Q hQ).map_source
    (realSchurMixedRotatedLocalChart_zero_mem_source B T hT hdiag hsep Q hQ)
  change Q*(realSchurMixedExpCoordinates (fun i => (B i).size) T 0)*Qᵀ ∈ _ at h
  simpa [realSchurMixedExpCoordinates_zero] using h

#print axioms realSchurMixedRotatedLocalChart_center_mem_target
end SpectralRadiusUpperTail
