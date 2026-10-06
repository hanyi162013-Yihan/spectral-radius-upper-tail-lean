import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Ring.Equiv

namespace SpectralRadiusUpperTail

lemma ringEquiv_map_ringInverse {R S : Type*} [Ring R] [Ring S]
    (f : R ≃+* S) (x : R) : f (Ring.inverse x) = Ring.inverse (f x) := by
  by_cases hx : IsUnit x
  · obtain ⟨u,rfl⟩ := hx
    have hu : f (u : R) = ((Units.map f.toMonoidHom u : Sˣ) : S) := rfl
    rw [Ring.inverse_unit,hu,Ring.inverse_unit]
    simp
  · have hf : ¬ IsUnit (f x) := by
      intro hh
      have hback := hh.map f.symm.toMonoidHom
      exact hx (by simpa using hback)
    rw [Ring.inverse_non_unit _ hx,Ring.inverse_non_unit _ hf,map_zero]

#print axioms ringEquiv_map_ringInverse
end SpectralRadiusUpperTail
