import SpectralRadiusUpperTail.RealSchurMixedFlagRotated
import Mathlib.Topology.Bases

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

abbrev RealSchurMixedOrthogonalFrame {m : ℕ} (s : Fin m → ℕ) :=
  {R : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ // Rᵀ*R=1}

/-- Countably many rotated marker neighborhoods cover every ordered
orthogonal block flag. The neighborhoods are selected before any actual
Schur diagonal or strict-upper matrix entries are introduced. -/
theorem exists_countable_realSchurMixedFlagAtlas
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c) :
    ∃ C : Set (RealSchurMixedOrthogonalFrame s), C.Countable ∧
      ∀ Q : RealSchurMixedOrthogonalFrame s, ∃ R ∈ C,
        Q.val*realSchurMixedBlockScalar s c*Q.valᵀ ∈
          (realSchurMixedMarkerRotatedChart s hs c hc R.val R.property).target := by
  let : SecondCountableTopology
      (Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ) :=
    inferInstanceAs
      (SecondCountableTopology (RealSchurMixedCoord s → RealSchurMixedCoord s → ℝ))
  obtain ⟨C,hC,hcover⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun R : RealSchurMixedOrthogonalFrame s =>
      (realSchurMixedMarkerRotatedChart s hs c hc R.val R.property).target)
    (fun R => (realSchurMixedMarkerRotatedChart s hs c hc R.val R.property).open_target)
  refine ⟨C,hC,?_⟩
  intro Q
  have hmem : Q.val*realSchurMixedBlockScalar s c*Q.valᵀ ∈
      ⋃ R : RealSchurMixedOrthogonalFrame s,
        (realSchurMixedMarkerRotatedChart s hs c hc R.val R.property).target :=
    Set.mem_iUnion_of_mem Q
      (realSchurMixedMarkerRotatedChart_center_mem_target s hs c hc Q.val Q.property)
  rw [← hcover] at hmem
  simpa only [Set.mem_iUnion, exists_prop] using hmem

theorem exists_realSchurMixedFlagAtlasSequence
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c) :
    ∃ R : ℕ → RealSchurMixedOrthogonalFrame s,
      ∀ Q : RealSchurMixedOrthogonalFrame s, ∃ k,
        Q.val*realSchurMixedBlockScalar s c*Q.valᵀ ∈
          (realSchurMixedMarkerRotatedChart s hs c hc (R k).val (R k).property).target := by
  classical
  obtain ⟨C,hC,hcover⟩ := exists_countable_realSchurMixedFlagAtlas s hs c hc
  have hne : C.Nonempty := by
    let Q : RealSchurMixedOrthogonalFrame s := ⟨1,by simp⟩
    obtain ⟨R,hR,_⟩ := hcover Q
    exact ⟨R,hR⟩
  obtain ⟨R,hR⟩ := hC.exists_eq_range hne
  refine ⟨R,?_⟩
  intro Q
  obtain ⟨P,hP,hmem⟩ := hcover Q
  have hp : P ∈ Set.range R := by simpa only [hR] using hP
  obtain ⟨k,hk⟩ := hp
  exact ⟨k,hk ▸ hmem⟩

#print axioms exists_countable_realSchurMixedFlagAtlas
#print axioms exists_realSchurMixedFlagAtlasSequence
end SpectralRadiusUpperTail
