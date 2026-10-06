import SpectralRadiusUpperTail.RealSchurMixedBlockRoots
import Mathlib.Data.Multiset.Bind
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The real root or the root in the open upper half-plane chosen from
one admissible real Schur block. -/
noncomputable def RealSchurChartBlock.canonicalRoot :
    RealSchurChartBlock → ℂ
  | .scalar a => (a : ℂ)
  | .pair x _ _ y _ _ => (x : ℂ)+(y : ℂ)*Complex.I

/-- Selecting roots in the closed upper half-plane leaves precisely
one canonical root per real Schur block. -/
theorem RealSchurChartBlock.filter_nonnegative_imag_roots
    (B : RealSchurChartBlock) :
    B.complexRoots.filter (fun z : ℂ => 0 ≤ z.im) =
      {B.canonicalRoot} := by
  classical
  cases B with
  | scalar a =>
      simp [RealSchurChartBlock.complexRoots,
        RealSchurChartBlock.canonicalRoot]
  | pair x b c y hbc hy =>
      have hpos : 0 ≤ ((x : ℂ)+(y : ℂ)*Complex.I).im := by
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, Complex.I_re,
          mul_one, mul_zero, add_zero, zero_add]
        exact le_of_lt hy
      have hneg : ¬ 0 ≤ ((x : ℂ)-(y : ℂ)*Complex.I).im := by
        simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, Complex.I_re,
          mul_one, mul_zero, add_zero, zero_add]
        linarith
      change Multiset.filter (fun z : ℂ => 0 ≤ z.im)
        (((x : ℂ)+(y : ℂ)*Complex.I) ::ₘ
          ({(x : ℂ)-(y : ℂ)*Complex.I} : Multiset ℂ)) =
        {((x : ℂ)+(y : ℂ)*Complex.I)}
      rw [Multiset.filter_cons_of_pos
        (p := fun z : ℂ => 0 ≤ z.im) _ hpos,
        Multiset.filter_singleton]
      simp [not_le.mpr hy]

/-- Filtering the complete block-root multiset by the upper
half-plane extracts the multiset of canonical block labels. -/
theorem realSchur_canonicalRoots_eq_filter_fullRoots
    {ι : Type*} [Fintype ι] (B : ι → RealSchurChartBlock) :
    ((Finset.univ : Finset ι).val.bind
      (fun i => (B i).complexRoots)).filter
        (fun z : ℂ => 0 ≤ z.im) =
      (Finset.univ : Finset ι).val.map
        (fun i => (B i).canonicalRoot) := by
  classical
  rw [Multiset.filter_bind]
  simp_rw [RealSchurChartBlock.filter_nonnegative_imag_roots]
  exact Multiset.bind_singleton _ _

#print axioms RealSchurChartBlock.filter_nonnegative_imag_roots
#print axioms realSchur_canonicalRoots_eq_filter_fullRoots
end SpectralRadiusUpperTail
