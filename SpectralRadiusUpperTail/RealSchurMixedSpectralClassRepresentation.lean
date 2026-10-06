import SpectralRadiusUpperTail.RealSchurMixedSpectralClassClosed
import SpectralRadiusUpperTail.RealSchurMixedChartSpectrum

namespace SpectralRadiusUpperTail
open Polynomial
open scoped Matrix Matrix.Norms.Operator

theorem realSchurMixedSpectralClass_mem_iff
    {m : ℕ} (s : Fin m → ℕ) (p : Fin m → ℝ[X])
    (A : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :
    A ∈ realSchurMixedSpectralClass s p ↔
      ∃ Q : RealSchurMixedOrthogonalFrame s,
        ∃ T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ,
          realSchurMixedLowerProjection s T=0 ∧
          (∀ a, (realSchurMixedDiagonalMatrix s T a).charpoly=p a) ∧
          A=Q.val*T*Q.valᵀ := by
  constructor
  · rintro ⟨Q,hT,hp⟩
    refine ⟨Q,Q.valᵀ*A*Q.val,hT,hp,?_⟩
    have hQQ := mul_eq_one_comm.mp Q.property
    calc
      A = (Q.val*Q.valᵀ)*A*(Q.val*Q.valᵀ) := by
        rw [hQQ,Matrix.one_mul,Matrix.mul_one]
      _ = Q.val*(Q.valᵀ*A*Q.val)*Q.valᵀ := by simp only [Matrix.mul_assoc]
  · rintro ⟨Q,T,hT,hp,rfl⟩
    have h : Q.valᵀ*(Q.val*T*Q.valᵀ)*Q.val=T := by
      calc
        _ = (Q.valᵀ*Q.val)*T*(Q.valᵀ*Q.val) := by simp only [Matrix.mul_assoc]
        _ = T := by rw [Q.property,Matrix.one_mul,Matrix.mul_one]
    exact ⟨Q,by simpa only [h] using hT,by simpa only [h] using hp⟩

#print axioms realSchurMixedSpectralClass_mem_iff
end SpectralRadiusUpperTail
