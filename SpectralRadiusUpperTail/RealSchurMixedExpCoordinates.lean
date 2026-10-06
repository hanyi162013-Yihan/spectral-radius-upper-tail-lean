import SpectralRadiusUpperTail.RealSchurMixedTangent
import Ginibre.ExpConjugation
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator RightActions

theorem realSchurMixedSkewEmbed_add
    {m : ℕ} (s : Fin m → ℕ)
    (ω η : RealSchurMixedOrbitIndex s → ℝ) :
    realSchurMixedSkewEmbed s (ω+η) =
      realSchurMixedSkewEmbed s ω + realSchurMixedSkewEmbed s η := by
  classical
  simp [realSchurMixedSkewEmbed, Pi.add_apply, add_smul,
    Finset.sum_add_distrib]

theorem realSchurMixedSkewEmbed_smul
    {m : ℕ} (s : Fin m → ℕ) (a : ℝ)
    (ω : RealSchurMixedOrbitIndex s → ℝ) :
    realSchurMixedSkewEmbed s (a • ω) =
      a • realSchurMixedSkewEmbed s ω := by
  classical
  simp only [realSchurMixedSkewEmbed, Pi.smul_apply,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact mul_smul a (ω q) (realSchurMixedOrbitGenerator s q)

/-- The skew angular embedding is a continuous real-linear map between
finite-dimensional spaces. -/
noncomputable def realSchurMixedSkewCLM
    {m : ℕ} (s : Fin m → ℕ) :
    (RealSchurMixedOrbitIndex s → ℝ) →L[ℝ]
      Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun := realSchurMixedSkewEmbed s
    map_add' := realSchurMixedSkewEmbed_add s
    map_smul' := realSchurMixedSkewEmbed_smul s }

/-- The local orthogonal-conjugation chart with its triangular matrix held
fixed. Its derivative at zero is the genuine skew commutator. -/
noncomputable def realSchurMixedAngularChart
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (ω : RealSchurMixedOrbitIndex s → ℝ) :
    Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ :=
  NormedSpace.exp (realSchurMixedSkewCLM s ω) * T *
    NormedSpace.exp (-realSchurMixedSkewCLM s ω)

noncomputable def realSchurMixedAngularFrame
    {m : ℕ} (s : Fin m → ℕ)
    (ω : RealSchurMixedOrbitIndex s → ℝ) :
    Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ :=
  NormedSpace.exp (realSchurMixedSkewCLM s ω)

/-- The angular exponential is an actual orthogonal matrix. -/
theorem realSchurMixedAngularFrame_orthogonal
    {m : ℕ} (s : Fin m → ℕ)
    (ω : RealSchurMixedOrbitIndex s → ℝ) :
    (realSchurMixedAngularFrame s ω)ᵀ *
      realSchurMixedAngularFrame s ω = 1 := by
  change (NormedSpace.exp (realSchurMixedSkewEmbed s ω))ᵀ *
    NormedSpace.exp (realSchurMixedSkewEmbed s ω) = 1
  rw [← Matrix.exp_transpose, realSchurMixedSkewEmbed_transpose,
    Matrix.exp_neg]
  exact Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _))

theorem realSchurMixedAngularChart_eq_conjugation
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (ω : RealSchurMixedOrbitIndex s → ℝ) :
    realSchurMixedAngularChart s T ω =
      realSchurMixedAngularFrame s ω * T *
        (realSchurMixedAngularFrame s ω)ᵀ := by
  unfold realSchurMixedAngularChart realSchurMixedAngularFrame
  have hskew : ((realSchurMixedSkewCLM s) ω)ᵀ =
      -((realSchurMixedSkewCLM s) ω) :=
    realSchurMixedSkewEmbed_transpose s ω
  rw [← hskew, Matrix.exp_transpose]

def realSchurMixedAngularChart_hasStrictFDerivAt_zero
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :=
  Ginibre.hasStrictFDerivAt_exp_conjugation T
    (realSchurMixedSkewCLM s) 0

#print axioms realSchurMixedAngularChart_hasStrictFDerivAt_zero
#print axioms realSchurMixedAngularFrame_orthogonal
#print axioms realSchurMixedAngularChart_eq_conjugation
end SpectralRadiusUpperTail
