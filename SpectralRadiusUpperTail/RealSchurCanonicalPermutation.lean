import SpectralRadiusUpperTail.RealSchurCanonicalBlockIdentification
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- A simple complete root multiset determines the matching of the
real and upper-half-plane Schur blocks, even across different block
orders and shapes. -/
theorem realSchur_exists_matchingBlockEquiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : ι → RealSchurChartBlock)
    (C : κ → RealSchurChartBlock)
    (hroots : ((Finset.univ : Finset ι).val.bind
        (fun i => (B i).complexRoots)) =
      ((Finset.univ : Finset κ).val.bind
        (fun j => (C j).complexRoots)))
    (hnodup : ((Finset.univ : Finset ι).val.bind
        (fun i => (B i).complexRoots)).Nodup) :
    ∃ e : ι ≃ κ, ∀ i,
      (B i).canonicalRoot = (C (e i)).canonicalRoot ∧
      (B i).size = (C (e i)).size ∧
      (B i).matrix.charpoly = (C (e i)).matrix.charpoly := by
  classical
  have hkeys := realSchur_canonicalRoot_multiset_eq_of_fullRoots_eq B C hroots
  have hnodupB : ((Finset.univ : Finset ι).val.map
      (fun i => (B i).canonicalRoot)).Nodup := by
    rw [← realSchur_canonicalRoots_eq_filter_fullRoots B]
    exact hnodup.filter _
  have hnodupC : ((Finset.univ : Finset κ).val.map
      (fun j => (C j).canonicalRoot)).Nodup := by
    rw [← hkeys]
    exact hnodupB
  have hinjB : Function.Injective (fun i : ι => (B i).canonicalRoot) := by
    intro i j hij
    exact Multiset.inj_on_of_nodup_map hnodupB i (by simp)
      j (by simp) hij
  have hinjC : Function.Injective (fun j : κ => (C j).canonicalRoot) := by
    intro i j hij
    exact Multiset.inj_on_of_nodup_map hnodupC i (by simp)
      j (by simp) hij
  have hex (i : ι) : ∃ j : κ,
      (C j).canonicalRoot = (B i).canonicalRoot := by
    have hm : (B i).canonicalRoot ∈
        (Finset.univ : Finset κ).val.map
          (fun j => (C j).canonicalRoot) := by
      rw [← hkeys]
      exact Multiset.mem_map_of_mem _ (by simp)
    obtain ⟨j,_,hj⟩ := Multiset.mem_map.mp hm
    exact ⟨j,hj⟩
  let f : ι → κ := fun i => Classical.choose (hex i)
  have hf (i : ι) : (C (f i)).canonicalRoot = (B i).canonicalRoot :=
    Classical.choose_spec (hex i)
  have hfinj : Function.Injective f := by
    intro i j hij
    apply hinjB
    calc
      (B i).canonicalRoot = (C (f i)).canonicalRoot := (hf i).symm
      _ = (C (f j)).canonicalRoot := by rw [hij]
      _ = (B j).canonicalRoot := hf j
  have hfsurj : Function.Surjective f := by
    intro j
    have hm : (C j).canonicalRoot ∈
        (Finset.univ : Finset ι).val.map
          (fun i => (B i).canonicalRoot) := by
      rw [hkeys]
      exact Multiset.mem_map_of_mem _ (by simp)
    obtain ⟨i,_,hi⟩ := Multiset.mem_map.mp hm
    refine ⟨i, ?_⟩
    apply hinjC
    change (C (f i)).canonicalRoot = (C j).canonicalRoot
    exact (hf i).trans hi
  let e : ι ≃ κ := Equiv.ofBijective f ⟨hfinj,hfsurj⟩
  refine ⟨e, ?_⟩
  intro i
  have hkey : (B i).canonicalRoot = (C (e i)).canonicalRoot :=
    (hf i).symm
  exact ⟨hkey,
    (RealSchurChartBlock.size_charpoly_eq_of_canonicalRoot_eq
      (B i) (C (e i)) hkey).1,
    (RealSchurChartBlock.size_charpoly_eq_of_canonicalRoot_eq
      (B i) (C (e i)) hkey).2⟩

#print axioms realSchur_exists_matchingBlockEquiv
end SpectralRadiusUpperTail
