import SpectralRadiusUpperTail.RealSchurMixedRegularChart
import Mathlib.Topology.Bases
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A regular real mixed-Schur frame with an actual block-upper center. -/
structure RealSchurMixedRegularFrame {m : ℕ} (s : Fin m → ℕ) where
  T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ
  upper : realSchurMixedLowerProjection s T = 0
  regular : (realSchurMixedOrbitMatrix s T).det ≠ 0
  Q : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ
  orthogonal : Qᵀ*Q=1

/-- The local inverse-function chart belonging to a regular frame. -/
noncomputable def RealSchurMixedRegularFrame.chart {m : ℕ}
    {s : Fin m → ℕ} (c : RealSchurMixedRegularFrame s) :
    OpenPartialHomeomorph (RealSchurMixedTangent s)
      (Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :=
  realSchurMixedRegularRotatedChart s c.T c.regular c.Q c.orthogonal

theorem RealSchurMixedRegularFrame.center_mem_target {m : ℕ}
    {s : Fin m → ℕ} (c : RealSchurMixedRegularFrame s) :
    c.Q*c.T*c.Qᵀ ∈ c.chart.target :=
  realSchurMixedRegularRotatedChart_center_mem_target
    s c.T c.regular c.Q c.orthogonal

/-- One family of regular charts can be selected countably, in advance,
and it covers every matrix having a regular block-upper representation
of the specified shape. No global Schur-existence claim is hidden here. -/
theorem exists_countable_realSchurMixedRegularAtlas
    {m : ℕ} (s : Fin m → ℕ) :
    ∃ C : Set (RealSchurMixedRegularFrame s), C.Countable ∧
      ∀ (T Q : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ),
        realSchurMixedLowerProjection s T = 0 →
        (realSchurMixedOrbitMatrix s T).det ≠ 0 →
        Qᵀ*Q=1 →
        ∃ c ∈ C, Q*T*Qᵀ ∈ c.chart.target := by
  let : SecondCountableTopology
      (Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :=
    inferInstanceAs
      (SecondCountableTopology (RealSchurMixedCoord s → RealSchurMixedCoord s → ℝ))
  obtain ⟨C, hc, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun c : RealSchurMixedRegularFrame s => c.chart.target)
    (fun c => c.chart.open_target)
  refine ⟨C, hc, ?_⟩
  intro T Q hT hdet hQ
  let c : RealSchurMixedRegularFrame s := ⟨T, hT, hdet, Q, hQ⟩
  have hmem : Q*T*Qᵀ ∈ ⋃ d : RealSchurMixedRegularFrame s, d.chart.target :=
    Set.mem_iUnion_of_mem c c.center_mem_target
  rw [← hcover] at hmem
  simpa only [Set.mem_iUnion, exists_prop] using hmem

#print axioms exists_countable_realSchurMixedRegularAtlas
end SpectralRadiusUpperTail
