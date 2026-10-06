import Mathlib.Data.Setoid.Basic

namespace SpectralRadiusUpperTail
variable {α β : Type*}

lemma quotientAssignment_kernel (r : Setoid α) (f : Quotient r → β)
    (hf : Function.Injective f) : Setoid.ker (fun a => f (Quotient.mk r a)) = r := by
  apply Setoid.ext
  intro a b
  change f (Quotient.mk r a) = f (Quotient.mk r b) ↔ r a b
  rw [hf.eq_iff, Quotient.eq]

/-- Assignments with exactly one prescribed equality pattern correspond
 bijectively to injective assignments on its quotient vertices. -/
noncomputable def equalityPatternEquiv (r : Setoid α) :
    {x : α → β // Setoid.ker x = r} ≃
      {f : Quotient r → β // Function.Injective f} where
  toFun x := ⟨Quotient.lift x.1 x.2.ge,
    (Setoid.lift_injective_iff_ker_eq_of_le x.2.ge).mpr x.2⟩
  invFun f := ⟨fun a => f.1 (Quotient.mk r a), quotientAssignment_kernel r f.1 f.2⟩
  left_inv x := by
    apply Subtype.ext
    funext a
    rfl
  right_inv f := by
    apply Subtype.ext
    funext q
    induction q using Quotient.inductionOn with
    | _ a => rfl

lemma equalityPatternEquiv_apply_mk (r : Setoid α)
    (x : {x : α → β // Setoid.ker x = r}) (a : α) :
    (equalityPatternEquiv r x).1 (Quotient.mk r a) = x.1 a := rfl

#print axioms quotientAssignment_kernel
#print axioms equalityPatternEquiv
#print axioms equalityPatternEquiv_apply_mk
end SpectralRadiusUpperTail
