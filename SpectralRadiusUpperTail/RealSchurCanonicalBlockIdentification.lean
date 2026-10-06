import SpectralRadiusUpperTail.RealSchurCanonicalRootKeys
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- Equal canonical roots identify the block type and its characteristic
polynomial; the internal real 2×2 coordinates may still differ. -/
theorem RealSchurChartBlock.size_charpoly_eq_of_canonicalRoot_eq
    (B C : RealSchurChartBlock)
    (h : B.canonicalRoot = C.canonicalRoot) :
    B.size = C.size ∧ B.matrix.charpoly = C.matrix.charpoly := by
  cases B with
  | scalar a =>
      cases C with
      | scalar u =>
          have hau : a = u := by
            change (a : ℂ) = (u : ℂ) at h
            exact_mod_cast h
          subst u
          exact ⟨rfl,rfl⟩
      | pair x b c y hbc hy =>
          have him := congrArg Complex.im h
          have hyzero : y = 0 := by
            simpa [RealSchurChartBlock.canonicalRoot,
              Complex.add_im, Complex.mul_im] using him.symm
          exact (False.elim ((ne_of_gt hy) hyzero))
  | pair x b c y hbc hy =>
      cases C with
      | scalar u =>
          have him := congrArg Complex.im h
          have hyzero : y = 0 := by
            simpa [RealSchurChartBlock.canonicalRoot,
              Complex.add_im, Complex.mul_im] using him
          exact (False.elim ((ne_of_gt hy) hyzero))
      | pair u d e v hde hv =>
          have hre := congrArg Complex.re h
          have him := congrArg Complex.im h
          have hxu : x = u := by
            simpa [RealSchurChartBlock.canonicalRoot,
              Complex.add_re, Complex.mul_re] using hre
          have hyv : y = v := by
            simpa [RealSchurChartBlock.canonicalRoot,
              Complex.add_im, Complex.mul_im] using him
          subst u
          subst v
          constructor
          · rfl
          · rw [RealSchurChartBlock.charpoly_eq_polynomial,
              RealSchurChartBlock.charpoly_eq_polynomial]
            rfl

/-- Equality of complete root multisets implies equality of the
canonical block-label multisets, even when the two lists have
different numbers or orderings of blocks. -/
theorem realSchur_canonicalRoot_multiset_eq_of_fullRoots_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : ι → RealSchurChartBlock)
    (C : κ → RealSchurChartBlock)
    (h : ((Finset.univ : Finset ι).val.bind
        (fun i => (B i).complexRoots)) =
      ((Finset.univ : Finset κ).val.bind
        (fun j => (C j).complexRoots))) :
    (Finset.univ : Finset ι).val.map
        (fun i => (B i).canonicalRoot) =
      (Finset.univ : Finset κ).val.map
        (fun j => (C j).canonicalRoot) := by
  rw [← realSchur_canonicalRoots_eq_filter_fullRoots B,
    ← realSchur_canonicalRoots_eq_filter_fullRoots C, h]

#print axioms RealSchurChartBlock.size_charpoly_eq_of_canonicalRoot_eq
#print axioms realSchur_canonicalRoot_multiset_eq_of_fullRoots_eq
end SpectralRadiusUpperTail
