import SpectralRadiusUpperTail.MarkedRealChartImageIntegration
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Set
open scoped Matrix

private abbrev MarkedMatrix (m : ℕ) :=
  Matrix (RealSchurMixedCoord (markedRealTwoBlockSizes m))
    (RealSchurMixedCoord (markedRealTwoBlockSizes m)) ℝ

/-- Restricting a first branch in the ambient product to the incidence
subtype gives exactly the marked-root first patch. -/
theorem markedRealIncidenceFirstPatch_iff_productFirstPatch
    (m : ℕ) (b : ℝ)
    (c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m))
    (k : ℕ) (p : MarkedRealSimpleRootIncidence m b) :
    p ∈ markedRealIncidenceFirstPatch m b c k ↔
      p.val ∈ markedRealProductFirstPatch m c k := by
  simp only [markedRealIncidenceFirstPatch, markedRealProductFirstPatch,
    markedRealIncidenceChartBranch, Set.mem_diff, Set.mem_iUnion]
  rfl

/-- The matrix image of one local source patch is precisely the
projection of its corresponding marked-root incidence patch. -/
theorem markedRealChartFirstSource_matrixImage
    (m : ℕ) (hm : 0 < m) (b : ℝ)
    (c : ℕ → RealSchurMixedRegularFrame (markedRealTwoBlockSizes m))
    (k : ℕ) :
    (c k).chart '' markedRealChartFirstSource m b c k =
      markedRealSimpleRootProjection m b ''
        markedRealIncidenceFirstPatch m b c k := by
  ext A
  constructor
  · rintro ⟨t,ht,rfl⟩
    rcases ht with ⟨⟨⟨htarget,hpatch⟩,hsep⟩,hcut⟩
    let x := markedRealScalar m ((c k).T+t.2.val)
    let p : MarkedRealSimpleRootIncidence m b :=
      ⟨((c k).chart t,x),
        ⟨hsep, markedRealChart_scalar_isRoot m hm (c k) t, hcut⟩⟩
    refine ⟨p, ?_, rfl⟩
    exact (markedRealIncidenceFirstPatch_iff_productFirstPatch
      m b c k p).mpr hpatch
  · rintro ⟨p,hp,hA⟩
    have hpatch : p.val ∈ markedRealProductFirstPatch m c k :=
      (markedRealIncidenceFirstPatch_iff_productFirstPatch
        m b c k p).mp hp
    have hbranch : p.val ∈ markedRealChartBranch m (c k) := hpatch.1
    let t := (c k).chart.symm p.val.1
    have htarget : p.val.1 ∈ (c k).chart.target := hbranch.1
    have hsource : t ∈ (c k).chart.source :=
      (c k).chart.map_target htarget
    have hchart : (c k).chart t = p.val.1 :=
      (c k).chart.right_inv htarget
    have hx : p.val.2 = markedRealScalar m ((c k).T+t.2.val) :=
      markedRealChartBranch_root_eq_scalar m hm (c k)
        p.val hbranch p.property.2.1
    have hpatch' :
        ((c k).chart t,
          markedRealScalar m ((c k).T+t.2.val)) ∈
            markedRealProductFirstPatch m c k := by
      rw [hchart, ← hx]
      exact hpatch
    have hsep : ((c k).chart t).charpoly.Separable := by
      rw [hchart]
      exact p.property.1
    have hcut : b < markedRealScalar m ((c k).T+t.2.val) := by
      rw [← hx]
      exact p.property.2.2
    refine ⟨t, ⟨⟨⟨hsource,hpatch'⟩,hsep⟩,hcut⟩, ?_⟩
    exact hchart.trans hA

#print axioms markedRealIncidenceFirstPatch_iff_productFirstPatch
#print axioms markedRealChartFirstSource_matrixImage
end SpectralRadiusUpperTail
