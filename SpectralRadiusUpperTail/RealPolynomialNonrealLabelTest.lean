import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open Polynomial

/-- A real polynomial divisor has no real root exactly when every one
of its roots in a covering list of the ambient roots has nonzero imaginary part. -/
theorem realPolynomial_noRealRoot_iff_label_tests
    {ι : Type*} (p q : ℝ[X]) (hq : q ∣ p) (z : ι → ℂ)
    (hcover : ∀ w : ℂ, (p.map Complex.ofRealHom).eval w=0 → ∃ i, z i=w) :
    (∀ a : ℝ, q.eval a ≠ 0) ↔
      ∀ i, (q.map Complex.ofRealHom).eval (z i)=0 → (z i).im ≠ 0 := by
  constructor
  · intro hno i hi him
    have hz : z i=Complex.ofRealHom (z i).re := by
      apply Complex.ext <;> simp [him]
    rw [hz,Polynomial.eval_map_apply] at hi
    apply hno (z i).re
    change ((q.eval ((z i).re) : ℝ) : ℂ)=0 at hi
    exact_mod_cast hi
  · intro hno a ha
    have hp : p.eval a=0 := by
      obtain ⟨r,rfl⟩ := hq
      rw [Polynomial.eval_mul,ha,zero_mul]
    have hpc : (p.map Complex.ofRealHom).eval (Complex.ofRealHom a)=0 := by
      rw [Polynomial.eval_map_apply,hp,map_zero]
    obtain ⟨i,hi⟩ := hcover (Complex.ofRealHom a) hpc
    have hqc : (q.map Complex.ofRealHom).eval (z i)=0 := by
      rw [hi,Polynomial.eval_map_apply,ha,map_zero]
    apply hno i hqc
    rw [hi]
    rfl

#print axioms realPolynomial_noRealRoot_iff_label_tests
end SpectralRadiusUpperTail
