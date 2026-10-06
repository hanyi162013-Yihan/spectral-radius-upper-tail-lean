import SpectralRadiusUpperTail.MarkedRealAngularJacobianContinuous
import SpectralRadiusUpperTail.MarkedRealAngularRankGaussianArea
import SpectralRadiusUpperTail.RealSchurMixedAngleRestIntegral
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Classical
open scoped ENNReal Matrix Matrix.Norms.Operator

/-- Angular density on the fixed oriented chart. -/
noncomputable def markedRealAngularWeight (m : ℕ)
    (ω : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ) : ℝ≥0∞ :=
  if ω ∈ markedRealAngularPositiveSource m then
    ENNReal.ofReal |realSchurMixedAngularJacobian
      (markedRealTwoBlockSizes m) ω|
  else 0

theorem markedRealAngularWeight_measurable (m : ℕ) :
    Measurable (markedRealAngularWeight m) := by
  unfold markedRealAngularWeight
  have hset : MeasurableSet (markedRealAngularPositiveSource m) :=
    (isOpen_markedRealAngularPositiveSource m).measurableSet
  have hval : Measurable
      (fun ω : RealSchurMixedOrbitIndex (markedRealTwoBlockSizes m) → ℝ =>
        ENNReal.ofReal |realSchurMixedAngularJacobian
          (markedRealTwoBlockSizes m) ω|) :=
    (markedRealAngularJacobian_continuous m).abs.measurable.ennreal_ofReal
  exact Measurable.ite hset hval measurable_const

/-- Diagonal/upper-entry density on one rank layer, with no angular
coordinate. The free upper row is still present at this stage. -/
noncomputable def markedRealRankRestWeight
    (m k : ℕ) (b : ℝ)
    (z : (RealSchurMixedDiagonalEntry (markedRealTwoBlockSizes m) → ℝ) ×
      (RealSchurMixedStrictUpperEntry (markedRealTwoBlockSizes m) → ℝ)) :
    ℝ≥0∞ :=
  let S := (realSchurMixedUpperEntryEquiv
    (markedRealTwoBlockSizes m)).symm z
  if S ∈ markedRealUpperRankSource m k b then
    ENNReal.ofReal
      |(markedRealComplement m S.val -
        markedRealScalar m S.val •
          (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
      ENNReal.ofReal (realMatrixGaussianWeight
        (RealSchurMixedCoord (markedRealTwoBlockSizes m)) S.val)
  else 0

theorem markedRealRankRestWeight_measurable
    (m k : ℕ) (b : ℝ) :
    Measurable (markedRealRankRestWeight m k b) := by
  let s := markedRealTwoBlockSizes m
  let U := realSchurMixedUpperSubmodule s
  let S : ((RealSchurMixedDiagonalEntry s → ℝ) ×
      (RealSchurMixedStrictUpperEntry s → ℝ)) → U :=
    (realSchurMixedUpperEntryEquiv s).symm
  have hS : Measurable S :=
    (realSchurMixedUpperEntryEquiv s).symm.toContinuousLinearEquiv.continuous.measurable
  have hguard : MeasurableSet (S ⁻¹' markedRealUpperRankSource m k b) :=
    (measurableSet_markedRealUpperRankSource m k b).preimage hS
  have hdetMatrix : Continuous
      (fun A : Matrix (RealSchurMixedCoord s)
        (RealSchurMixedCoord s) ℝ =>
        (markedRealComplement m A - markedRealScalar m A •
          (1 : Matrix (Fin m) (Fin m) ℝ)).det) := by
    have hmat : Continuous
        (fun A : Matrix (RealSchurMixedCoord s)
          (RealSchurMixedCoord s) ℝ =>
          markedRealComplement m A - markedRealScalar m A •
            (1 : Matrix (Fin m) (Fin m) ℝ)) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      simp only [Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply]
      fun_prop
    exact hmat.matrix_det
  have hdet : Measurable (fun T : U =>
      ENNReal.ofReal
        |(markedRealComplement m T.val - markedRealScalar m T.val •
          (1 : Matrix (Fin m) (Fin m) ℝ)).det|) :=
    (hdetMatrix.comp continuous_subtype_val).abs.measurable.ennreal_ofReal
  have hgaussMatrix : Continuous
      (realMatrixGaussianWeight (RealSchurMixedCoord s)) := by
    unfold realMatrixGaussianWeight
    fun_prop
  have hgauss : Measurable (fun T : U =>
      ENNReal.ofReal (realMatrixGaussianWeight
        (RealSchurMixedCoord s) T.val)) :=
    (hgaussMatrix.comp continuous_subtype_val).measurable.ennreal_ofReal
  change Measurable (fun z =>
    if S z ∈ markedRealUpperRankSource m k b then
      ENNReal.ofReal
        |(markedRealComplement m (S z).val -
            markedRealScalar m (S z).val •
              (1 : Matrix (Fin m) (Fin m) ℝ)).det| *
        ENNReal.ofReal (realMatrixGaussianWeight
          (RealSchurMixedCoord s) (S z).val)
    else 0)
  exact Measurable.ite hguard
    ((hdet.comp hS).mul (hgauss.comp hS)) measurable_const

#print axioms markedRealAngularWeight_measurable
#print axioms markedRealRankRestWeight_measurable
end SpectralRadiusUpperTail
