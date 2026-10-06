import SpectralRadiusUpperTail.MarkedRealComplementEvalContinuous
import SpectralRadiusUpperTail.RealSchurMixedRegularAtlas
import SpectralRadiusUpperTail.RealSchurMixedRegularGaussianIntegration
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Set
open scoped Matrix

private abbrev MarkedMatrix (m : ℕ) :=
  Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
    (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ

/-- The part of one regular Schur chart on which the complementary block
does not share the proposed root. This is a branch in matrix-root space,
not merely a subset of matrices. -/
noncomputable def markedRealChartBranch (m : ℕ)
    (c : RealSchurMixedRegularFrame (markedRealTwoBlockSizes m)) :
    Set (MarkedMatrix m × ℝ) :=
  {p | p.1 ∈ c.chart.target ∧
    (markedRealComplement m
      (c.T + (c.chart.symm p.1).2.val)).charpoly.eval p.2 ≠ 0}

theorem isOpen_markedRealChartBranch (m : ℕ)
    (c : RealSchurMixedRegularFrame (markedRealTwoBlockSizes m)) :
    IsOpen (markedRealChartBranch m c) := by
  let D : Set (MarkedMatrix m × ℝ) :=
    (fun p => p.1) ⁻¹' c.chart.target
  have hD : IsOpen D := c.chart.open_target.preimage continuous_fst
  have hsymm : ContinuousOn (fun p : MarkedMatrix m × ℝ =>
      c.chart.symm p.1) D := by
    apply c.chart.continuousOn_symm.comp continuous_fst.continuousOn
    intro p hp
    exact hp
  have hpair : ContinuousOn (fun p : MarkedMatrix m × ℝ =>
      (c.T + (c.chart.symm p.1).2.val, p.2)) D := by
    fun_prop
  have hgap : ContinuousOn (fun p : MarkedMatrix m × ℝ =>
      (markedRealComplement m
        (c.T + (c.chart.symm p.1).2.val)).charpoly.eval p.2) D :=
    (continuous_markedRealComplement_charpoly_eval m).comp_continuousOn hpair
  have hopen := hgap.isOpen_inter_preimage hD
    (isOpen_compl_singleton : IsOpen ({(0 : ℝ)}ᶜ))
  convert hopen using 1
  ext p
  simp [markedRealChartBranch, D]

/-- A point of the marked branch has precisely the scalar root selected
by the inverse local Schur chart. -/
theorem markedRealChartBranch_root_eq_scalar
    (m : ℕ) (hm : 0 < m)
    (c : RealSchurMixedRegularFrame (markedRealTwoBlockSizes m))
    (p : MarkedMatrix m × ℝ)
    (hp : p ∈ markedRealChartBranch m c)
    (hroot : p.1.charpoly.IsRoot p.2) :
    p.2 = markedRealScalar m
      (c.T + (c.chart.symm p.1).2.val) := by
  let t := c.chart.symm p.1
  have htarget : p.1 ∈ c.chart.target := hp.1
  have hA : c.chart t = p.1 := c.chart.right_inv htarget
  have hexp :
      c.Q*(realSchurMixedExpCoordinates (markedRealTwoBlockSizes m) c.T t)*c.Qᵀ =
        p.1 := by
    simpa only [RealSchurMixedRegularFrame.chart,
      realSchurMixedRegularRotatedChart_apply] using hA
  have hroot' :
      (c.Q*(realSchurMixedExpCoordinates (markedRealTwoBlockSizes m) c.T t)*c.Qᵀ).charpoly.IsRoot p.2 := by
    rw [hexp]
    exact hroot
  exact markedRealTwoBlock_rotatedChart_root_unique m hm
    c.T c.Q c.upper c.orthogonal t p.2 hroot' hp.2

/-- The marked center of a simple-spectrum regular Schur frame belongs
to its own open root branch. -/
theorem markedRealChartBranch_center_mem
    (m : ℕ) (hm : 0 < m)
    (c : RealSchurMixedRegularFrame (markedRealTwoBlockSizes m))
    (hsep : c.T.charpoly.Separable) :
    (c.Q*c.T*c.Qᵀ, markedRealScalar m c.T) ∈
      markedRealChartBranch m c := by
  have hzero : (0 : RealSchurMixedTangent (markedRealTwoBlockSizes m)) ∈
      c.chart.source :=
    realSchurMixedRegularChart_zero_mem_source
      (markedRealTwoBlockSizes m) c.T c.regular
  have hcenter : c.chart
      (0 : RealSchurMixedTangent (markedRealTwoBlockSizes m)) =
      c.Q*c.T*c.Qᵀ := by
    rw [RealSchurMixedRegularFrame.chart,
      realSchurMixedRegularRotatedChart_apply,
      realSchurMixedExpCoordinates_zero]
  have hinv : c.chart.symm (c.Q*c.T*c.Qᵀ) =
      (0 : RealSchurMixedTangent (markedRealTwoBlockSizes m)) := by
    rw [← hcenter]
    exact c.chart.left_inv hzero
  constructor
  · exact c.center_mem_target
  · rw [hinv]
    have hdet := markedRealTwoBlock_complement_det_ne_zero
      m hm c.T c.upper hsep
    have hneg :
        markedRealComplement m c.T - markedRealScalar m c.T •
          (1 : Matrix (Fin m) (Fin m) ℝ) =
        -(markedRealScalar m c.T •
          (1 : Matrix (Fin m) (Fin m) ℝ) - markedRealComplement m c.T) := by
      abel
    have hdet' :
        (markedRealScalar m c.T •
          (1 : Matrix (Fin m) (Fin m) ℝ) - markedRealComplement m c.T).det ≠ 0 := by
      intro hh
      rw [hneg, Matrix.det_neg, hh, mul_zero] at hdet
      exact hdet rfl
    have hzeroVal :
        ((0 : RealSchurMixedTangent (markedRealTwoBlockSizes m)).2.val :
          Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
            (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ) = 0 := rfl
    have hscalar :
        Matrix.scalar (Fin m) (markedRealScalar m c.T) =
          markedRealScalar m c.T • (1 : Matrix (Fin m) (Fin m) ℝ) := by
      ext i j
      simp [Matrix.scalar_apply, Matrix.diagonal_apply,
        Matrix.smul_apply, Matrix.one_apply]
    simpa only [hzeroVal, add_zero, Matrix.eval_charpoly, hscalar] using hdet'

#print axioms isOpen_markedRealChartBranch
#print axioms markedRealChartBranch_root_eq_scalar
#print axioms markedRealChartBranch_center_mem
end SpectralRadiusUpperTail
