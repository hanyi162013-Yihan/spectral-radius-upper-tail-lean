import SpectralRadiusUpperTail.MarkedRealRootIncidence
import SpectralRadiusUpperTail.CountableChartFiberCount
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Set

/-- The incidence space of real eigenvalue marks above a cutoff. -/
abbrev PositiveMarkedRealIncidence (n : ℕ) (b : ℝ) :=
  {p : Matrix (Fin n) (Fin n) ℝ × ℝ //
    p.1.charpoly.IsRoot p.2 ∧ b < p.2}

/-- Forget the mark while retaining the matrix. -/
abbrev positiveMarkedRealProjection (n : ℕ) (b : ℝ) :
    PositiveMarkedRealIncidence n b → Matrix (Fin n) (Fin n) ℝ :=
  fun p => p.val.1

/-- The fiber of the marked incidence projection is exactly the set of
real characteristic roots above the cutoff, without multiplicity. -/
def positiveMarkedRealFiberEquiv (n : ℕ) (b : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    {p : PositiveMarkedRealIncidence n b //
      positiveMarkedRealProjection n b p = A} ≃
      {x : ℝ // A.charpoly.IsRoot x ∧ b < x} where
  toFun p := by
    refine ⟨p.val.val.2, ?_⟩
    have hA : p.val.val.1 = A := p.property
    simpa only [hA] using p.val.property
  invFun x :=
    ⟨⟨(A, x.val), x.property⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact p.property.symm
    · rfl
  right_inv x := by
    apply Subtype.ext
    rfl

/-- Any countable disjoint atlas in the marked incidence space that covers
the entire fiber counts each real root exactly once in its image sum. -/
theorem positiveMarkedRealAtlas_fiberCount
    (n : ℕ) (b : ℝ)
    (s : ℕ → Set (PositiveMarkedRealIncidence n b))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hinj : ∀ k, InjOn (positiveMarkedRealProjection n b) (s k))
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hcover : ∀ p : PositiveMarkedRealIncidence n b,
      positiveMarkedRealProjection n b p = A → p ∈ ⋃ k, s k) :
    {k : ℕ | A ∈ positiveMarkedRealProjection n b '' s k}.encard =
      {x : ℝ | A.charpoly.IsRoot x ∧ b < x}.encard := by
  have hfull :
      positiveMarkedRealProjection n b ⁻¹' {A} ∩ ⋃ k, s k =
        positiveMarkedRealProjection n b ⁻¹' {A} := by
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    constructor
    · exact And.left
    · intro hp
      exact ⟨hp, hcover p hp⟩
  rw [← countableChartFiber_encard
    (positiveMarkedRealProjection n b) s hd hinj A, hfull]
  exact Set.encard_congr (positiveMarkedRealFiberEquiv n b A)

#print axioms positiveMarkedRealFiberEquiv
#print axioms positiveMarkedRealAtlas_fiberCount
end SpectralRadiusUpperTail
