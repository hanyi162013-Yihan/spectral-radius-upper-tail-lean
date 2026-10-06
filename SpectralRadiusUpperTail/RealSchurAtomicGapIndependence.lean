import SpectralRadiusUpperTail.RealSchurCanonicalDiagonalGap
import SpectralRadiusUpperTail.RealSchurAtomicDiagonalWeightInvariance
import Mathlib.Analysis.Convex.Topology

namespace SpectralRadiusUpperTail
open scoped Matrix ENNReal

/-- At a fixed simple spectrum the actual atlas overlap correction is
independent of all positive pair-gap coordinates. -/
theorem realSchurAtomicMultiplicityWeight_gap_independent
    {n : ℕ} (F : RealSchurFiniteAtlas n) (I : RealSchurFiniteCode n) (k : ℕ)
    (x u a b : Fin I.1.blockCount → ℝ)
    (hu : ∀ i, I.1.sizes i=2 → 0 < u i)
    (ha : ∀ i, I.1.sizes i=2 → 0 < a i)
    (hb : ∀ i, I.1.sizes i=2 → 0 < b i)
    (hsep : (realSchurMixedUpperEntryJoin I.1.sizes
      (realSchurCanonicalDiagonal I.1.sizes x u a) 0).charpoly.Separable) :
    realSchurAtomicDiagonalMultiplicityWeight F I k (realSchurCanonicalDiagonal I.1.sizes x u a)=
      realSchurAtomicDiagonalMultiplicityWeight F I k (realSchurCanonicalDiagonal I.1.sizes x u b) := by
  let X := Set.Icc (0 : ℝ) 1
  let : PreconnectedSpace X := Subtype.preconnectedSpace (convex_Icc (0 : ℝ) 1).isPreconnected
  let g : X → Fin I.1.blockCount → ℝ := fun t i => (1-t.val)*a i+t.val*b i
  let d := fun t : X => realSchurCanonicalDiagonal I.1.sizes x u (g t)
  have hg (t : X) (i : Fin I.1.blockCount) (hi : I.1.sizes i=2) : 0 < g t i := by
    exact (convex_Ioi (0 : ℝ)) (ha i hi) (hb i hi)
      (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
  have hd : Continuous d := by
    apply (realSchurCanonicalDiagonal_continuous_gap I.1.sizes x u).comp
    apply continuous_pi
    intro i
    dsimp only [g]
    fun_prop
  have hp (t : X) : (realSchurMixedUpperEntryJoin I.1.sizes (d t) 0).charpoly=
      (realSchurMixedUpperEntryJoin I.1.sizes (realSchurCanonicalDiagonal I.1.sizes x u a) 0).charpoly :=
    realSchurCanonicalDiagonal_charpoly_gap I.1.sizes I.1.sizes_pos I.1.sizes_small
      x u (g t) a hu (hg t) ha
  have hsep' (t : X) : (realSchurMixedUpperEntryJoin I.1.sizes (d t) 0).charpoly.Separable := by
    rw [hp t]
    exact hsep
  have hh := realSchurAtomicDiagonalMultiplicityWeight_connected F I k d hd hsep'
    (fun t w => (hp t).trans (hp w).symm)
    (⟨0,by constructor <;> norm_num⟩ : X) (⟨1,by constructor <;> norm_num⟩ : X)
  simpa only [d,g,sub_zero,one_mul,zero_mul,add_zero,sub_self,mul_one,zero_add] using hh

#print axioms realSchurAtomicMultiplicityWeight_gap_independent
end SpectralRadiusUpperTail
