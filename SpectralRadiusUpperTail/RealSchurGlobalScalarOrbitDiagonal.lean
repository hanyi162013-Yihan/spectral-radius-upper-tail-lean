import SpectralRadiusUpperTail.RealSchurScalarScalarOrbitFactor
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- In any dimension, the coefficient of a single skew mixing direction
in its own matrix-entry coordinate is the difference of the two diagonal
entries. This is the diagonal factor of the global scalar-block Schur
orbit Jacobian; off-diagonal coupling among directions remains separate. -/
theorem realSchur_scalar_orbit_diagonal_coefficient
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) (hij : i ≠ j) (t : ℝ) :
    let K : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.single i j t - Matrix.single j i t
    (K*T-T*K) i j = t*(T j j-T i i) := by
  dsimp
  simp [Matrix.sub_apply, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.single_mul_apply_same, Matrix.mul_single_apply_same,
    Matrix.single_mul_apply_of_ne, Matrix.mul_single_apply_of_ne,
    hij, hij.symm]
  ring

/-- Exact action of one skew mixing direction on every matrix entry. It
isolates the interactions with other Schur directions that must be ordered
when computing the full Jacobian determinant. -/
theorem realSchur_scalar_orbit_direction_action
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (i j p q : Fin n) (t : ℝ) :
    let K : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.single i j t - Matrix.single j i t
    (K*T-T*K) p q =
      (if p = i then t*T j q else 0) -
      (if p = j then t*T i q else 0) -
      (if q = j then T p i*t else 0) +
      (if q = i then T p j*t else 0) := by
  have hL1 : (Matrix.single i j t * T) p q =
      if p = i then t*T j q else 0 := by
    by_cases h : p = i
    · subst p
      simp
    · rw [Matrix.single_mul_apply_of_ne (h := h)]
      simp [h]
  have hL2 : (Matrix.single j i t * T) p q =
      if p = j then t*T i q else 0 := by
    by_cases h : p = j
    · subst p
      simp
    · rw [Matrix.single_mul_apply_of_ne (h := h)]
      simp [h]
  have hR1 : (T * Matrix.single i j t) p q =
      if q = j then T p i*t else 0 := by
    by_cases h : q = j
    · subst q
      simp
    · rw [Matrix.mul_single_apply_of_ne (hbj := h)]
      simp [h]
  have hR2 : (T * Matrix.single j i t) p q =
      if q = i then T p j*t else 0 := by
    by_cases h : q = i
    · subst q
      simp
    · rw [Matrix.mul_single_apply_of_ne (hbj := h)]
      simp [h]
  dsimp
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_apply,
    hL1, hL2, hR1, hR2]
  ring

/-- For an upper-triangular scalar Schur matrix, a skew direction at
distance `i-j` below the diagonal cannot affect a lower entry farther
from the diagonal. This is the triangular ordering behind the product of
scalar spectral-gap factors in the global orbit Jacobian. -/
theorem realSchur_scalar_orbit_distance_support
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ a b : Fin n, b < a → T a b = 0)
    (i j p q : Fin n) (hij : j < i) (hpq : q < p)
    (hfar : i.val-j.val < p.val-q.val) (t : ℝ) :
    let K : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.single i j t - Matrix.single j i t
    (K*T-T*K) p q = 0 := by
  have h1 : (if p = i then t*T j q else 0) = 0 := by
    by_cases hpi : p = i
    · have hqj : q < j := by
        apply Fin.lt_def.mpr
        have hji : j.val < i.val := hij
        have hqp : q.val < p.val := hpq
        omega
      simp [hpi, hT j q hqj]
    · simp [hpi]
  have h2 : (if p = j then t*T i q else 0) = 0 := by
    by_cases hpj : p = j
    · have hqi : q < i := lt_of_lt_of_le hpq (by simpa [hpj] using hij.le)
      simp [hpj, hT i q hqi]
    · simp [hpj]
  have h3 : (if q = j then T p i*t else 0) = 0 := by
    by_cases hqj : q = j
    · have hip : i < p := by
        apply Fin.lt_def.mpr
        have hji : j.val < i.val := hij
        have hqp : q.val < p.val := hpq
        omega
      simp [hqj, hT p i hip]
    · simp [hqj]
  have h4 : (if q = i then T p j*t else 0) = 0 := by
    by_cases hqi : q = i
    · have hjp : j < p := lt_trans hij (by simpa [hqi] using hpq)
      simp [hqi, hT p j hjp]
    · simp [hqi]
  change ((Matrix.single i j t - Matrix.single j i t)*T -
    T*(Matrix.single i j t - Matrix.single j i t)) p q = 0
  rw [realSchur_scalar_orbit_direction_action T i j p q t,
    h1, h2, h3, h4]
  ring

/-- At a fixed distance below the diagonal, distinct scalar mixing
directions do not couple. Together with distance support, this makes the
scalar-block orbit Jacobian triangular with the spectral-gap coefficients
on its diagonal. -/
theorem realSchur_scalar_orbit_same_distance_offdiagonal
    {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ)
    (hT : ∀ a b : Fin n, b < a → T a b = 0)
    (i j p q : Fin n) (hij : j < i) (hpq : q < p)
    (hdist : i.val-j.val = p.val-q.val)
    (hneq : (p,q) ≠ (i,j)) (t : ℝ) :
    let K : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.single i j t - Matrix.single j i t
    (K*T-T*K) p q = 0 := by
  have hpi : p ≠ i := by
    intro h
    have hq : q = j := by
      apply Fin.ext
      have hji : j.val < i.val := hij
      have hqp : q.val < p.val := hpq
      omega
    exact hneq (Prod.ext h hq)
  have hqj : q ≠ j := by
    intro h
    have hp : p = i := by
      apply Fin.ext
      have hji : j.val < i.val := hij
      have hqp : q.val < p.val := hpq
      omega
    exact hneq (Prod.ext hp h)
  have h2 : (if p = j then t*T i q else 0) = 0 := by
    by_cases hpj : p = j
    · have hqi : q < i := lt_of_lt_of_le hpq (by simpa [hpj] using hij.le)
      simp [hpj, hT i q hqi]
    · simp [hpj]
  have h4 : (if q = i then T p j*t else 0) = 0 := by
    by_cases hqi : q = i
    · have hjp : j < p := lt_trans hij (by simpa [hqi] using hpq)
      simp [hqi, hT p j hjp]
    · simp [hqi]
  change ((Matrix.single i j t - Matrix.single j i t)*T -
    T*(Matrix.single i j t - Matrix.single j i t)) p q = 0
  rw [realSchur_scalar_orbit_direction_action T i j p q t]
  simp [hpi, hqj, h2, h4]

#print axioms realSchur_scalar_orbit_diagonal_coefficient
#print axioms realSchur_scalar_orbit_direction_action
#print axioms realSchur_scalar_orbit_distance_support
#print axioms realSchur_scalar_orbit_same_distance_offdiagonal
end SpectralRadiusUpperTail
