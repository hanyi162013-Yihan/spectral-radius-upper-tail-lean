import SpectralRadiusUpperTail.MarkedRealChartBranchSequence
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Set

private abbrev MarkedMatrix (m : ℕ) :=
  Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
    (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ

/-- Assign each marked real root to its first open branch. The removal
of earlier branches happens in matrix-root space. -/
def markedRealIncidenceFirstPatch (m : ℕ) (b : ℝ)
    (c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m))
    (k : ℕ) : Set (MarkedRealSimpleRootIncidence m b) :=
  markedRealIncidenceChartBranch m b (c k) \
    ⋃ j ∈ Finset.range k, markedRealIncidenceChartBranch m b (c j)

theorem pairwise_markedRealIncidenceFirstPatch
    (m : ℕ) (b : ℝ)
    (c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m)) :
    Pairwise (fun i j => Disjoint
      (markedRealIncidenceFirstPatch m b c i)
      (markedRealIncidenceFirstPatch m b c j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro p hi hj
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hj.2 (Set.mem_iUnion_of_mem i
      (Set.mem_iUnion_of_mem (Finset.mem_range.mpr hij) hi.1))
  · exact hi.2 (Set.mem_iUnion_of_mem j
      (Set.mem_iUnion_of_mem (Finset.mem_range.mpr hji) hj.1))

theorem iUnion_markedRealIncidenceFirstPatch
    (m : ℕ) (b : ℝ)
    (c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m)) :
    (⋃ k, markedRealIncidenceFirstPatch m b c k) =
      ⋃ k, markedRealIncidenceChartBranch m b (c k) := by
  classical
  ext p
  constructor
  · intro h
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp h
    exact Set.mem_iUnion_of_mem k hk.1
  · intro h
    have hp : ∃ k, p ∈ markedRealIncidenceChartBranch m b (c k) :=
      Set.mem_iUnion.mp h
    let k := Nat.find hp
    refine Set.mem_iUnion_of_mem k ⟨Nat.find_spec hp, ?_⟩
    intro hearly
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hearly
    obtain ⟨hjk,hpj⟩ := Set.mem_iUnion.mp hj
    exact Nat.find_min hp (Finset.mem_range.mp hjk) hpj

/-- A countable, disjoint marked-root atlas covers the entire
simple-spectrum real-root incidence space above any cutoff. -/
theorem exists_markedRealIncidenceFirstPatch_cover
    (m : ℕ) (hm : 0 < m) (b : ℝ) :
    ∃ c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m),
      (⋃ k, markedRealIncidenceFirstPatch m b c k) = Set.univ := by
  obtain ⟨c,hcover⟩ := exists_markedRealChartBranch_sequence m hm
  refine ⟨c, ?_⟩
  rw [iUnion_markedRealIncidenceFirstPatch]
  ext p
  simp only [mem_iUnion, mem_univ, iff_true]
  obtain ⟨k,hk⟩ := hcover p.val.1 p.val.2
    p.property.1 p.property.2.1
  exact ⟨k,hk⟩

/-- On a simple-spectrum matrix, a marked incidence fiber is equivalent
to its set of real roots above the cutoff. -/
def markedRealSimpleRootFiberEquiv (m : ℕ) (b : ℝ)
    (A : MarkedMatrix m) (hsep : A.charpoly.Separable) :
    {p : MarkedRealSimpleRootIncidence m b //
      markedRealSimpleRootProjection m b p = A} ≃
      {x : ℝ // A.charpoly.IsRoot x ∧ b < x} where
  toFun p := by
    refine ⟨p.val.val.2, ?_⟩
    have hA : p.val.val.1 = A := p.property
    simpa only [hA] using p.val.property.2
  invFun x :=
    ⟨⟨(A, x.val), ⟨hsep, x.property⟩⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact p.property.symm
    · rfl
  right_inv x := by
    apply Subtype.ext
    rfl

/-- For a covering branch sequence, the image multiplicity of its
disjointified marked patches is exactly the number of distinct real
roots above the cutoff. -/
theorem markedRealIncidenceFirstPatch_fiberCount
    (m : ℕ) (hm : 0 < m) (b : ℝ)
    (c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m))
    (hcover :
      (⋃ k, markedRealIncidenceFirstPatch m b c k) = Set.univ)
    (A : MarkedMatrix m) (hsep : A.charpoly.Separable) :
    {k : ℕ | A ∈ markedRealSimpleRootProjection m b ''
      markedRealIncidenceFirstPatch m b c k}.encard =
      {x : ℝ | A.charpoly.IsRoot x ∧ b < x}.encard := by
  have hinj : ∀ k, InjOn (markedRealSimpleRootProjection m b)
      (markedRealIncidenceFirstPatch m b c k) := by
    intro k
    exact (markedRealIncidenceChartBranch_projection_inj m hm b (c k)).mono
      (Set.diff_subset)
  have hfull :
      markedRealSimpleRootProjection m b ⁻¹' {A} ∩
        ⋃ k, markedRealIncidenceFirstPatch m b c k =
        markedRealSimpleRootProjection m b ⁻¹' {A} := by
    rw [hcover, Set.inter_univ]
  rw [← countableChartFiber_encard
    (markedRealSimpleRootProjection m b)
    (markedRealIncidenceFirstPatch m b c)
    (pairwise_markedRealIncidenceFirstPatch m b c) hinj A, hfull]
  exact Set.encard_congr (markedRealSimpleRootFiberEquiv m b A hsep)

/-- One fixed branch sequence, selected independently of the cutoff,
counts every simple-spectrum matrix's real roots correctly. -/
theorem exists_markedRealIncidenceFirstPatch_fiberCount
    (m : ℕ) (hm : 0 < m) :
    ∃ c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m),
      ∀ (b : ℝ) (A : MarkedMatrix m), A.charpoly.Separable →
        {k : ℕ | A ∈ markedRealSimpleRootProjection m b ''
          markedRealIncidenceFirstPatch m b c k}.encard =
          {x : ℝ | A.charpoly.IsRoot x ∧ b < x}.encard := by
  obtain ⟨c,hc⟩ := exists_markedRealChartBranch_sequence m hm
  refine ⟨c, ?_⟩
  intro b A hsep
  apply markedRealIncidenceFirstPatch_fiberCount m hm b c ?_ A hsep
  rw [iUnion_markedRealIncidenceFirstPatch]
  ext p
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  obtain ⟨k,hk⟩ := hc p.val.1 p.val.2 p.property.1 p.property.2.1
  exact ⟨k,hk⟩

#print axioms pairwise_markedRealIncidenceFirstPatch
#print axioms iUnion_markedRealIncidenceFirstPatch
#print axioms exists_markedRealIncidenceFirstPatch_cover
#print axioms markedRealSimpleRootFiberEquiv
#print axioms markedRealIncidenceFirstPatch_fiberCount
#print axioms exists_markedRealIncidenceFirstPatch_fiberCount
end SpectralRadiusUpperTail
