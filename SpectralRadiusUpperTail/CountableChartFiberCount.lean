import SpectralRadiusUpperTail.CountableLocalAreaFormula
import Mathlib.Data.Set.Card
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open MeasureTheory Set
open scoped ENNReal

/-- Disjoint injective chart patches index the marked preimages of a
target point exactly once. -/
noncomputable def countableChartFiberEquiv
    {X Y : Type*} (f : X → Y) (s : ℕ → Set X)
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hinj : ∀ k, InjOn f (s k)) (y : Y) :
    {x : X // x ∈ f ⁻¹' {y} ∩ ⋃ k, s k} ≃
      {k : ℕ // y ∈ f '' s k} := by
  classical
  let q : {x : X // x ∈ f ⁻¹' {y} ∩ ⋃ k, s k} → ℕ :=
    fun x => Classical.choose (mem_iUnion.mp x.property.2)
  have hq (x : {x : X // x ∈ f ⁻¹' {y} ∩ ⋃ k, s k}) :
      x.val ∈ s (q x) := Classical.choose_spec (mem_iUnion.mp x.property.2)
  let g : {x : X // x ∈ f ⁻¹' {y} ∩ ⋃ k, s k} →
      {k : ℕ // y ∈ f '' s k} :=
    fun x => ⟨q x, ⟨x.val, hq x, x.property.1⟩⟩
  apply Equiv.ofBijective g
  constructor
  · intro x z h
    apply Subtype.ext
    have hqeq : q x = q z := congrArg Subtype.val h
    have hfx : f x = y := x.property.1
    have hfz : f z = y := z.property.1
    exact hinj (q x) (hq x) (by simpa only [hqeq] using hq z)
      (hfx.trans hfz.symm)
  · intro k
    obtain ⟨x, hx, hfx⟩ := k.property
    let z : {x : X // x ∈ f ⁻¹' {y} ∩ ⋃ j, s j} :=
      ⟨x, ⟨hfx, mem_iUnion_of_mem k.val hx⟩⟩
    refine ⟨z, Subtype.ext ?_⟩
    have hqk : q z = k.val := by
      by_contra hne
      exact (disjoint_left.mp (hd hne)) (hq z) hx
    exact hqk

theorem countableChartFiber_encard
    {X Y : Type*} (f : X → Y) (s : ℕ → Set X)
    (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hinj : ∀ k, InjOn f (s k)) (y : Y) :
    (f ⁻¹' {y} ∩ ⋃ k, s k).encard =
      {k : ℕ | y ∈ f '' s k}.encard :=
  Set.encard_congr (countableChartFiberEquiv f s hd hinj y)

#print axioms countableChartFiberEquiv
#print axioms countableChartFiber_encard
end SpectralRadiusUpperTail
