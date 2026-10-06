import SpectralRadiusUpperTail.RealSchurPairPairOrbitFactor
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- The diagonal coefficient of a global block Schur orbit is a Sylvester
operator, independently of all off-diagonal bridge blocks. The opposite
mixing block may be chosen to enforce skew symmetry without changing this
coordinate. -/
theorem realSchur_block_orbit_diagonal_coefficient
    {m : ℕ}
    (T : Matrix (Fin m) (Fin m) (Matrix (Fin 2) (Fin 2) ℝ))
    (i j : Fin m) (hij : i ≠ j)
    (X Y : Matrix (Fin 2) (Fin 2) ℝ) :
    let K : Matrix (Fin m) (Fin m) (Matrix (Fin 2) (Fin 2) ℝ) :=
      Matrix.single i j X + Matrix.single j i Y
    (K*T-T*K) i j = X*T j j - T i i*X := by
  dsimp
  simp [Matrix.sub_apply, Matrix.add_mul, Matrix.mul_add,
    Matrix.single_mul_apply_same, Matrix.mul_single_apply_same,
    Matrix.single_mul_apply_of_ne, Matrix.mul_single_apply_of_ne,
    hij, hij.symm]

/-- For the skew block direction, the same diagonal Sylvester coefficient
is obtained. -/
theorem realSchur_skew_block_orbit_diagonal_coefficient
    {m : ℕ}
    (T : Matrix (Fin m) (Fin m) (Matrix (Fin 2) (Fin 2) ℝ))
    (i j : Fin m) (hij : i ≠ j)
    (X : Matrix (Fin 2) (Fin 2) ℝ) :
    let K : Matrix (Fin m) (Fin m) (Matrix (Fin 2) (Fin 2) ℝ) :=
      Matrix.single i j X - Matrix.single j i Xᵀ
    (K*T-T*K) i j = X*T j j - T i i*X := by
  simpa only [sub_eq_add_neg, Matrix.single_neg] using
    realSchur_block_orbit_diagonal_coefficient T i j hij X (-Xᵀ)

/-- Entrywise action of one mixed-block direction. The formula is valid
for arbitrary (possibly noncommuting) square blocks. -/
theorem realSchur_block_orbit_direction_action
    {m : ℕ}
    (T : Matrix (Fin m) (Fin m) (Matrix (Fin 2) (Fin 2) ℝ))
    (i j p q : Fin m)
    (X Y : Matrix (Fin 2) (Fin 2) ℝ) :
    let K : Matrix (Fin m) (Fin m) (Matrix (Fin 2) (Fin 2) ℝ) :=
      Matrix.single i j X + Matrix.single j i Y
    (K*T-T*K) p q =
      (if p = i then X*T j q else 0) +
      (if p = j then Y*T i q else 0) -
      (if q = j then T p i*X else 0) -
      (if q = i then T p j*Y else 0) := by
  have hL1 : (Matrix.single i j X * T) p q =
      if p = i then X*T j q else 0 := by
    by_cases h : p = i
    · subst p
      simp
    · rw [Matrix.single_mul_apply_of_ne (h := h)]
      simp [h]
  have hL2 : (Matrix.single j i Y * T) p q =
      if p = j then Y*T i q else 0 := by
    by_cases h : p = j
    · subst p
      simp
    · rw [Matrix.single_mul_apply_of_ne (h := h)]
      simp [h]
  have hR1 : (T * Matrix.single i j X) p q =
      if q = j then T p i*X else 0 := by
    by_cases h : q = j
    · subst q
      simp
    · rw [Matrix.mul_single_apply_of_ne (hbj := h)]
      simp [h]
  have hR2 : (T * Matrix.single j i Y) p q =
      if q = i then T p j*Y else 0 := by
    by_cases h : q = i
    · subst q
      simp
    · rw [Matrix.mul_single_apply_of_ne (hbj := h)]
      simp [h]
  dsimp
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_apply,
    Matrix.add_apply, hL1, hL2, hR1, hR2]
  abel

/-- Upper-block-triangular Schur matrices have a triangular angular
Jacobian when lower-block coordinates are ordered by distance from the
diagonal: a direction cannot affect a more distant lower block. -/
theorem realSchur_block_orbit_distance_support
    {m : ℕ}
    (T : Matrix (Fin m) (Fin m) (Matrix (Fin 2) (Fin 2) ℝ))
    (hT : ∀ a b : Fin m, b < a → T a b = 0)
    (i j p q : Fin m) (hij : j < i) (hpq : q < p)
    (hfar : i.val-j.val < p.val-q.val)
    (X Y : Matrix (Fin 2) (Fin 2) ℝ) :
    let K : Matrix (Fin m) (Fin m) (Matrix (Fin 2) (Fin 2) ℝ) :=
      Matrix.single i j X + Matrix.single j i Y
    (K*T-T*K) p q = 0 := by
  have h1 : (if p = i then X*T j q else 0) = 0 := by
    by_cases hpi : p = i
    · have hqj : q < j := by
        apply Fin.lt_def.mpr
        have hji : j.val < i.val := hij
        have hqp : q.val < p.val := hpq
        omega
      simp [hpi, hT j q hqj]
    · simp [hpi]
  have h2 : (if p = j then Y*T i q else 0) = 0 := by
    by_cases hpj : p = j
    · have hqi : q < i := lt_of_lt_of_le hpq (by simpa [hpj] using hij.le)
      simp [hpj, hT i q hqi]
    · simp [hpj]
  have h3 : (if q = j then T p i*X else 0) = 0 := by
    by_cases hqj : q = j
    · have hip : i < p := by
        apply Fin.lt_def.mpr
        have hji : j.val < i.val := hij
        have hqp : q.val < p.val := hpq
        omega
      simp [hqj, hT p i hip]
    · simp [hqj]
  have h4 : (if q = i then T p j*Y else 0) = 0 := by
    by_cases hqi : q = i
    · have hjp : j < p := lt_trans hij (by simpa [hqi] using hpq)
      simp [hqi, hT p j hjp]
    · simp [hqi]
  change ((Matrix.single i j X + Matrix.single j i Y)*T -
    T*(Matrix.single i j X + Matrix.single j i Y)) p q = 0
  rw [realSchur_block_orbit_direction_action T i j p q X Y,
    h1, h2, h3, h4]
  simp

/-- Directions at the same lower-block distance are uncoupled unless
their block coordinates coincide. -/
theorem realSchur_block_orbit_same_distance_offdiagonal
    {m : ℕ}
    (T : Matrix (Fin m) (Fin m) (Matrix (Fin 2) (Fin 2) ℝ))
    (hT : ∀ a b : Fin m, b < a → T a b = 0)
    (i j p q : Fin m) (hij : j < i) (hpq : q < p)
    (hdist : i.val-j.val = p.val-q.val)
    (hneq : (p,q) ≠ (i,j))
    (X Y : Matrix (Fin 2) (Fin 2) ℝ) :
    let K : Matrix (Fin m) (Fin m) (Matrix (Fin 2) (Fin 2) ℝ) :=
      Matrix.single i j X + Matrix.single j i Y
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
  have h2 : (if p = j then Y*T i q else 0) = 0 := by
    by_cases hpj : p = j
    · have hqi : q < i := lt_of_lt_of_le hpq (by simpa [hpj] using hij.le)
      simp [hpj, hT i q hqi]
    · simp [hpj]
  have h4 : (if q = i then T p j*Y else 0) = 0 := by
    by_cases hqi : q = i
    · have hjp : j < p := lt_trans hij (by simpa [hqi] using hpq)
      simp [hqi, hT p j hjp]
    · simp [hqi]
  change ((Matrix.single i j X + Matrix.single j i Y)*T -
    T*(Matrix.single i j X + Matrix.single j i Y)) p q = 0
  rw [realSchur_block_orbit_direction_action T i j p q X Y]
  simp [hpi, hqj, h2, h4]

/-- When the two global diagonal blocks are real Schur conjugate-pair
blocks, the diagonal orbit coefficient is exactly the pair–pair Sylvester
matrix previously shown to have the two spectral-gap factors as its
determinant. The sign reflects the direction convention. -/
theorem realSchur_global_pair_pair_orbit_coefficient
    {m : ℕ}
    (T : Matrix (Fin m) (Fin m) (Matrix (Fin 2) (Fin 2) ℝ))
    (i j : Fin m) (hij : i ≠ j)
    (x b c u d e : ℝ)
    (hii : T i i = realSchurBlock x b c)
    (hjj : T j j = realSchurBlock u d e)
    (X : Matrix (Fin 2) (Fin 2) ℝ) :
    let K : Matrix (Fin m) (Fin m) (Matrix (Fin 2) (Fin 2) ℝ) :=
      Matrix.single i j X - Matrix.single j i Xᵀ
    realSchurBridgeVector ((K*T-T*K) i j) =
      -(realSchurPairPairSylvester x b c u d e).mulVec
        (realSchurBridgeVector X) := by
  have horbit := realSchur_skew_block_orbit_diagonal_coefficient
    T i j hij X
  dsimp at horbit ⊢
  rw [horbit, hii, hjj]
  have hflip : X*realSchurBlock u d e - realSchurBlock x b c*X =
      -(realSchurBlock x b c*X-X*realSchurBlock u d e) := by
    abel
  rw [hflip]
  have hvec (M : Matrix (Fin 2) (Fin 2) ℝ) :
      realSchurBridgeVector (-M) = -realSchurBridgeVector M := by
    funext k
    fin_cases k <;> simp [realSchurBridgeVector]
  rw [hvec, realSchur_pair_pair_sylvester_action]

#print axioms realSchur_block_orbit_diagonal_coefficient
#print axioms realSchur_skew_block_orbit_diagonal_coefficient
#print axioms realSchur_block_orbit_direction_action
#print axioms realSchur_block_orbit_distance_support
#print axioms realSchur_block_orbit_same_distance_offdiagonal
#print axioms realSchur_global_pair_pair_orbit_coefficient
end SpectralRadiusUpperTail
