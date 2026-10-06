import SpectralRadiusUpperTail.PolynomialComparison
import Mathlib.Data.Matrix.Basic

namespace SpectralRadiusUpperTail
open scoped BigOperators
open MvPolynomial
variable {n : ℕ}

def entryMatrix (x : (Fin n × Fin n) → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => x (i,j)

noncomputable def genericEntryMatrix (n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℕ) :=
  fun i j => X (i,j)

noncomputable def frobeniusPowerPolynomial (n k : ℕ) : MvPolynomial (Fin n × Fin n) ℕ :=
  ∑ i, ∑ j, (((genericEntryMatrix n)^k) i j)^2

def frobeniusPowerSquared (k : ℕ) (x : (Fin n × Fin n) → ℝ) : ℝ :=
  ∑ i, ∑ j, (((entryMatrix x)^k) i j)^2

lemma eval_genericEntryMatrix (x : (Fin n × Fin n) → ℝ) :
    (genericEntryMatrix n).map (eval₂Hom (Nat.castRingHom ℝ) x) = entryMatrix x := by
  ext i j
  exact eval₂_X (Nat.castRingHom ℝ) x (i,j)

lemma eval_genericMatrix_power (x : (Fin n × Fin n) → ℝ) (k : ℕ) (i j : Fin n) :
    evalNatPolynomial (((genericEntryMatrix n)^k) i j) x = ((entryMatrix x)^k) i j := by
  have h := Matrix.map_pow (genericEntryMatrix n) (eval₂Hom (Nat.castRingHom ℝ) x) k
  rw [eval_genericEntryMatrix] at h
  exact congrFun (congrFun h i) j

/-- The actual squared Frobenius power is a polynomial with natural coefficients. -/
theorem eval_frobeniusPowerPolynomial (x : (Fin n × Fin n) → ℝ) (k : ℕ) :
    evalNatPolynomial (frobeniusPowerPolynomial n k) x = frobeniusPowerSquared k x := by
  unfold frobeniusPowerPolynomial frobeniusPowerSquared evalNatPolynomial
  simp only [eval₂_sum, eval₂_pow]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show eval₂ (Nat.castRingHom ℝ) x (((genericEntryMatrix n)^k) i j) =
    ((entryMatrix x)^k) i j from eval_genericMatrix_power x k i j]

theorem frobeniusPowerSquared_nonneg (k : ℕ) (x : (Fin n × Fin n) → ℝ) :
    0 ≤ frobeniusPowerSquared k x := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))

#print axioms eval_genericMatrix_power
#print axioms eval_frobeniusPowerPolynomial
end SpectralRadiusUpperTail
