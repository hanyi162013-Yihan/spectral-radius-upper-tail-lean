import SpectralRadiusUpperTail.RealSchurMixedOrbitRegular
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

theorem realSchurMixedOrbitGenerator_transpose
    {m : ℕ} (s : Fin m → ℕ) (q : RealSchurMixedOrbitIndex s) :
    (realSchurMixedOrbitGenerator s q)ᵀ =
      -realSchurMixedOrbitGenerator s q := by
  dsimp [realSchurMixedOrbitGenerator]
  rw [Matrix.transpose_add, Matrix.transpose_single, Matrix.transpose_single]
  simp only [Matrix.single_neg, neg_add_rev]
  abel

/-- A vector of lower-block angular parameters defines an actual
skew-symmetric matrix, including the forced upper-block entries. -/
def realSchurMixedSkewEmbed {m : ℕ} (s : Fin m → ℕ)
    (ω : RealSchurMixedOrbitIndex s → ℝ) :
    Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ :=
  ∑ q, ω q • realSchurMixedOrbitGenerator s q

theorem realSchurMixedSkewEmbed_transpose
    {m : ℕ} (s : Fin m → ℕ)
    (ω : RealSchurMixedOrbitIndex s → ℝ) :
    (realSchurMixedSkewEmbed s ω)ᵀ = -realSchurMixedSkewEmbed s ω := by
  classical
  ext a b
  simp only [realSchurMixedSkewEmbed, Matrix.transpose_apply,
    Matrix.sum_apply, Matrix.neg_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro q _
  have hq := congrArg (fun M : Matrix (RealSchurMixedCoord s)
      (RealSchurMixedCoord s) ℝ => M a b)
    (realSchurMixedOrbitGenerator_transpose s q)
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at hq
  rw [hq]
  ring

/-- The lower-block part of the commutator with this genuine skew tangent
vector is precisely the mixed angular Jacobian applied to its coordinates. -/
theorem realSchurMixedSkewEmbed_lower_action
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (ω : RealSchurMixedOrbitIndex s → ℝ)
    (p : RealSchurMixedOrbitIndex s) :
    (realSchurMixedSkewEmbed s ω*T - T*realSchurMixedSkewEmbed s ω)
      ⟨p.1.1.1,p.2.1⟩ ⟨p.1.1.2,p.2.2⟩ =
        (realSchurMixedOrbitMatrix s T).mulVec ω p := by
  classical
  simp only [realSchurMixedSkewEmbed, Finset.sum_mul, Finset.mul_sum,
    Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_apply, Matrix.mulVec, dotProduct,
    realSchurMixedOrbitMatrix]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Matrix.sub_apply, smul_eq_mul]
  ring

#print axioms realSchurMixedSkewEmbed_transpose
#print axioms realSchurMixedSkewEmbed_lower_action
end SpectralRadiusUpperTail
