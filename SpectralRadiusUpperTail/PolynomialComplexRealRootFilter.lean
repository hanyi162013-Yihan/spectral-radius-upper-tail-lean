import SpectralRadiusUpperTail.PolynomialSimpleRealRootCount
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Polynomial

theorem complex_ofRealHom_mem_range_iff (z : ℂ) :
    z ∈ Complex.ofRealHom.range ↔ z.im = 0 := by
  constructor
  · rintro ⟨x,rfl⟩
    simp
  · intro hz
    refine ⟨z.re, ?_⟩
    apply Complex.ext <;> simp [hz]

/-- Among complex roots of a real polynomial, the roots on the real
axis are exactly the embedded real roots, with multiplicity preserved. -/
theorem realPolynomial_aroots_filter_real (p : ℝ[X]) :
    (p.aroots ℂ).filter (fun z => z.im = 0) =
      p.roots.map (fun x : ℝ => (x : ℂ)) := by
  classical
  have h := Polynomial.filter_roots_map_range_eq_map_roots
    (f := Complex.ofRealHom) Complex.ofReal_injective p
  have hfilter :
      (p.map Complex.ofRealHom).roots.filter (fun z : ℂ => z.im = 0) =
        (p.map Complex.ofRealHom).roots.filter
          (fun z : ℂ => z ∈ Complex.ofRealHom.range) := by
    apply Multiset.filter_congr
    intro z _
    exact (complex_ofRealHom_mem_range_iff z).symm
  calc
    (p.aroots ℂ).filter (fun z => z.im = 0) =
        (p.map Complex.ofRealHom).roots.filter (fun z : ℂ => z.im = 0) := rfl
    _ = _ := hfilter
    _ = p.roots.map (fun x : ℝ => (x : ℂ)) := by
      simpa using h

theorem realPolynomial_complexPositiveRealCount_eq_realCount
    (p : ℝ[X]) (t : ℝ) :
    Multiset.countP (fun z : ℂ => z.im = 0 ∧ t < z.re) (p.aroots ℂ) =
      Multiset.countP (fun x : ℝ => t < x) p.roots := by
  classical
  calc
    Multiset.countP (fun z : ℂ => z.im = 0 ∧ t < z.re) (p.aroots ℂ) =
        Multiset.countP (fun z : ℂ => t < z.re)
          ((p.aroots ℂ).filter (fun z => z.im = 0)) := by
      simp [Multiset.countP_eq_card_filter, Multiset.filter_filter, and_comm]
    _ = Multiset.countP (fun z : ℂ => t < z.re)
          (p.roots.map (fun x : ℝ => (x : ℂ))) := by
      rw [realPolynomial_aroots_filter_real]
    _ = Multiset.countP (fun x : ℝ => t < x) p.roots := by
      rw [Multiset.countP_map]
      simpa only [Complex.ofReal_re] using
        (Multiset.countP_eq_card_filter (fun x : ℝ => t < x) p.roots).symm

#print axioms realPolynomial_aroots_filter_real
#print axioms realPolynomial_complexPositiveRealCount_eq_realCount
end SpectralRadiusUpperTail
