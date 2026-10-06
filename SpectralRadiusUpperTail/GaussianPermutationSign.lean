import SpectralRadiusUpperTail.GaussianPrincipalMinorExpansion
import Mathlib.Tactic

namespace SpectralRadiusUpperTail

/-- The real coefficient of a determinant permutation term has square one. -/
theorem real_perm_sign_sq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι) :
    (((Equiv.Perm.sign π : ℤ) : ℝ)^2) = 1 := by
  have h := Int.units_mul_self (Equiv.Perm.sign π)
  rw [pow_two]
  have hz : ((Equiv.Perm.sign π : ℤ) * (Equiv.Perm.sign π : ℤ)) = 1 := by
    simpa only [Units.val_mul, Units.val_one] using congrArg Units.val h
  exact_mod_cast hz

#print axioms real_perm_sign_sq_one
end SpectralRadiusUpperTail
