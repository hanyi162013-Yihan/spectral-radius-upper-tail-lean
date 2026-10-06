import SpectralRadiusUpperTail.IncreasingPathCount
import Mathlib.Order.Fin.Tuple

namespace SpectralRadiusUpperTail

/-- Split a nontrivial strictly increasing Schur block path into its
first vertex and its strictly increasing tail. -/
noncomputable def increasingPathConsEquiv (N l : ℕ) :
    IncreasingBlockPath N (l+1) ≃
      {p : Fin N × IncreasingBlockPath N l // p.1 < p.2.val 0} where
  toFun p := ⟨(p.val 0, ⟨Fin.tail p.val, by
    intro a b hab
    exact p.property (by simpa using hab)⟩),
    p.property (by simp)⟩
  invFun p := ⟨Fin.cons p.val.1 p.val.2.val,
    (Fin.strictMono_cons).2 ⟨fun j =>
      p.property.trans_le (p.val.2.property.monotone (Fin.zero_le j)),
      p.val.2.property⟩⟩
  left_inv p := by
    apply Subtype.ext
    exact Fin.cons_self_tail p.val
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl

#print axioms increasingPathConsEquiv
end SpectralRadiusUpperTail
