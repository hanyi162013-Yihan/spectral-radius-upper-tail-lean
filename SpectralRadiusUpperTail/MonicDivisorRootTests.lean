import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Separable

namespace SpectralRadiusUpperTail

/-- A monic divisor of a simple complex polynomial is determined by
which roots of that polynomial it contains. -/
theorem complexMonicDivisors_eq_of_root_tests
    (p q r : Polynomial ℂ) (hp : p.Separable)
    (hq : q.Monic) (hr : r.Monic) (hqp : q ∣ p) (hrp : r ∣ p)
    (hroot : ∀ z : ℂ, p.eval z=0 → (q.eval z=0 ↔ r.eval z=0)) :
    q=r := by
  have hroots : q.roots=r.roots := by
    apply (Multiset.Nodup.ext (Polynomial.nodup_roots (hp.of_dvd hqp))
      (Polynomial.nodup_roots (hp.of_dvd hrp))).mpr
    intro z
    rw [Polynomial.mem_roots hq.ne_zero, Polynomial.mem_roots hr.ne_zero]
    constructor
    · intro hz
      exact (hroot z (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hqp hz)).mp hz
    · intro hz
      exact (hroot z (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hrp hz)).mpr hz
  rw [(IsAlgClosed.splits q).eq_prod_roots_of_monic hq,
    (IsAlgClosed.splits r).eq_prod_roots_of_monic hr, hroots]

/-- Testing a finite list that contains every root is enough. This
gives a finite code for ordered diagonal-block spectral factors. -/
theorem complexMonicDivisors_eq_of_label_tests
    {ι : Type*} (z : ι → ℂ) (p q r : Polynomial ℂ)
    (hp : p.Separable) (hq : q.Monic) (hr : r.Monic)
    (hqp : q ∣ p) (hrp : r ∣ p)
    (hcover : ∀ w : ℂ, p.eval w=0 → ∃ i, z i=w)
    (htest : ∀ i, q.eval (z i)=0 ↔ r.eval (z i)=0) : q=r := by
  apply complexMonicDivisors_eq_of_root_tests p q r hp hq hr hqp hrp
  intro w hw
  obtain ⟨i,rfl⟩ := hcover w hw
  exact htest i

#print axioms complexMonicDivisors_eq_of_root_tests
#print axioms complexMonicDivisors_eq_of_label_tests
end SpectralRadiusUpperTail
