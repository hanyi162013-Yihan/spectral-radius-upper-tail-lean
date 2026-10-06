import SpectralRadiusUpperTail.FiniteRealMatrixObservables
import SpectralRadiusUpperTail.FiniteMatrixPowerReindex
import SpectralRadiusUpperTail.RealSchurFiniteAtlasOutput
import SpectralRadiusUpperTail.RealGaussianShiftedRadiusMoment

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Frobenius

theorem finiteRealMatrixRadius_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (A : Matrix ι ι ℝ) (c : ℝ) :
    finiteRealMatrixRadius (c • Matrix.reindex e e A)=finiteRealMatrixRadius (c • A) := by
  have he : c • Matrix.reindex e e A=Matrix.reindex e e (c • A) := rfl
  rw [he]
  exact finiteRealMatrixRadius_eq_of_charpoly _ _ (Matrix.charpoly_reindex e (c • A))

theorem RealSchurFiniteAtlas.output_power_energy {n : ℕ}
    (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (j : ℕ)
    (t : RealSchurMixedTangent I.1.sizes) (c : ℝ) (k : ℕ) (hk : 0 < k) :
    scaledFrobeniusPowerSquared c k (F.output I j t)=‖(c • t.2.val)^k‖^2 := by
  change (∑ a, ∑ b, (((c • Matrix.of (F.output I j t).curry)^k) a b)^2)=_
  rw [← real_frobenius_norm_sq,F.output_matrix,
    finite_frobenius_reindex_power_norm_sq,
    finiteRealMatrixPower_conjugation _ _ (F.frames I j).property c k hk,
    realSchurMixedExpCoordinates_eq_conjugation,zero_add,
    finiteRealMatrixPower_conjugation _ _ (realSchurMixedAngularFrame_orthogonal I.1.sizes t.1) c k hk]

theorem RealSchurFiniteAtlas.output_radius {n : ℕ}
    (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (j : ℕ)
    (t : RealSchurMixedTangent I.1.sizes) (c : ℝ) :
    realMatrixRadius (c • entryMatrix (F.output I j t))=finiteRealMatrixRadius (c • t.2.val) := by
  change finiteRealMatrixRadius (c • Matrix.of (F.output I j t).curry)=_
  rw [F.output_matrix,finiteRealMatrixRadius_reindex,
    finiteRealMatrixRadius_conjugation _ _ (F.frames I j).property c,
    realSchurMixedExpCoordinates_eq_conjugation,zero_add,
    finiteRealMatrixRadius_conjugation _ _ (realSchurMixedAngularFrame_orthogonal I.1.sizes t.1) c]

#print axioms finiteRealMatrixRadius_reindex
#print axioms RealSchurFiniteAtlas.output_power_energy
#print axioms RealSchurFiniteAtlas.output_radius
end SpectralRadiusUpperTail
