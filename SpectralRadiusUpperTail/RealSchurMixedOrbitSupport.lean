import SpectralRadiusUpperTail.RealSchurMixedOrbitDiagonal
import Mathlib.Tactic

namespace SpectralRadiusUpperTail
open scoped Matrix

/-- A mixed-block skew direction cannot affect a lower block farther from
the diagonal. The block sizes do not enter this order argument. -/
theorem realSchurMixedOrbitMatrix_distance_support
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : ∀ a b : Fin m, b < a → ∀ x : Fin (s a),
      ∀ y : Fin (s b), T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (p q : RealSchurLowerIndex m)
    (r : RealSchurMixedBridge s p) (z : RealSchurMixedBridge s q)
    (hfar : realSchurLowerDistance q < realSchurLowerDistance p) :
    realSchurMixedOrbitMatrix s T ⟨p,r⟩ ⟨q,z⟩ = 0 := by
  let row : RealSchurMixedCoord s := ⟨p.1.1,r.1⟩
  let col : RealSchurMixedCoord s := ⟨p.1.2,r.2⟩
  let u : RealSchurMixedCoord s := ⟨q.1.1,z.1⟩
  let v : RealSchurMixedCoord s := ⟨q.1.2,z.2⟩
  have hf : q.1.1.val-q.1.2.val < p.1.1.val-p.1.2.val := hfar
  have h1 : (if row=u then -T v col else 0) = 0 := by
    split_ifs with h
    · have hi : p.1.1 = q.1.1 := congrArg Sigma.fst h
      have hj : p.1.2 < q.1.2 := by
        apply Fin.lt_def.mpr
        have hp := p.2
        have hq := q.2
        omega
      rw [show T v col = 0 from hT q.1.2 p.1.2 hj z.2 r.2]
      simp
    · rfl
  have h2 : (if row=v then T u col else 0) = 0 := by
    split_ifs with h
    · have hi : p.1.1 = q.1.2 := congrArg Sigma.fst h
      have hj : p.1.2 < q.1.1 := by
        apply Fin.lt_def.mpr
        have hp := p.2
        have hq := q.2
        omega
      exact hT q.1.1 p.1.2 hj z.1 r.2
    · rfl
  have h3 : (if col=v then -T row u else 0) = 0 := by
    split_ifs with h
    · have hj : p.1.2 = q.1.2 := congrArg Sigma.fst h
      have hi : q.1.1 < p.1.1 := by
        apply Fin.lt_def.mpr
        have hp := p.2
        have hq := q.2
        omega
      rw [show T row u = 0 from hT p.1.1 q.1.1 hi r.1 z.1]
      simp
    · rfl
  have h4 : (if col=u then T row v else 0) = 0 := by
    split_ifs with h
    · have hj : p.1.2 = q.1.1 := congrArg Sigma.fst h
      have hi : q.1.2 < p.1.1 := by
        apply Fin.lt_def.mpr
        have hp := p.2
        have hq := q.2
        omega
      exact hT p.1.1 q.1.2 hi r.1 z.2
    · rfl
  change ((Matrix.single u v (-1 : ℝ) + Matrix.single v u (1 : ℝ))*T -
    T*(Matrix.single u v (-1 : ℝ) + Matrix.single v u (1 : ℝ))) row col = 0
  rw [matrix_skew_single_commutator_apply T u v row col]
  simp [h1,h2,h3,h4]

/-- Different lower blocks at the same distance have no angular coupling. -/
theorem realSchurMixedOrbitMatrix_same_distance_offdiagonal
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : ∀ a b : Fin m, b < a → ∀ x : Fin (s a),
      ∀ y : Fin (s b), T ⟨a,x⟩ ⟨b,y⟩ = 0)
    (p q : RealSchurLowerIndex m)
    (r : RealSchurMixedBridge s p) (z : RealSchurMixedBridge s q)
    (hdist : realSchurLowerDistance q = realSchurLowerDistance p)
    (hneq : q ≠ p) :
    realSchurMixedOrbitMatrix s T ⟨p,r⟩ ⟨q,z⟩ = 0 := by
  let row : RealSchurMixedCoord s := ⟨p.1.1,r.1⟩
  let col : RealSchurMixedCoord s := ⟨p.1.2,r.2⟩
  let u : RealSchurMixedCoord s := ⟨q.1.1,z.1⟩
  let v : RealSchurMixedCoord s := ⟨q.1.2,z.2⟩
  have hd : q.1.1.val-q.1.2.val = p.1.1.val-p.1.2.val :=
    congrArg Fin.val hdist
  have hpi : p.1.1 ≠ q.1.1 := by
    intro hi
    have hj : p.1.2 = q.1.2 := by
      apply Fin.ext
      have hp := p.2
      have hq := q.2
      omega
    exact hneq (Subtype.ext (Prod.ext hi.symm hj.symm))
  have hpj : p.1.2 ≠ q.1.2 := by
    intro hj
    have hi : p.1.1 = q.1.1 := by
      apply Fin.ext
      have hp := p.2
      have hq := q.2
      omega
    exact hneq (Subtype.ext (Prod.ext hi.symm hj.symm))
  have h1 : (if row=u then -T v col else 0) = 0 := by
    simp [show row ≠ u from fun h => hpi (congrArg Sigma.fst h)]
  have h2 : (if row=v then T u col else 0) = 0 := by
    split_ifs with h
    · have hi : p.1.1 = q.1.2 := congrArg Sigma.fst h
      have hj : p.1.2 < q.1.1 := by
        apply Fin.lt_def.mpr
        have hp := p.2
        have hq := q.2
        omega
      exact hT q.1.1 p.1.2 hj z.1 r.2
    · rfl
  have h3 : (if col=v then -T row u else 0) = 0 := by
    simp [show col ≠ v from fun h => hpj (congrArg Sigma.fst h)]
  have h4 : (if col=u then T row v else 0) = 0 := by
    split_ifs with h
    · have hj : p.1.2 = q.1.1 := congrArg Sigma.fst h
      have hi : q.1.2 < p.1.1 := by
        apply Fin.lt_def.mpr
        have hp := p.2
        have hq := q.2
        omega
      exact hT p.1.1 q.1.2 hi r.1 z.2
    · rfl
  change ((Matrix.single u v (-1 : ℝ) + Matrix.single v u (1 : ℝ))*T -
    T*(Matrix.single u v (-1 : ℝ) + Matrix.single v u (1 : ℝ))) row col = 0
  rw [matrix_skew_single_commutator_apply T u v row col]
  simp [h1,h2,h3,h4]

/-- The mixed-size angular matrix is triangular by lower-block distance. -/
theorem realSchurMixedOrbitMatrix_blockTriangular
    {m : ℕ} (s : Fin m → ℕ)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : ∀ a b : Fin m, b < a → ∀ x : Fin (s a),
      ∀ y : Fin (s b), T ⟨a,x⟩ ⟨b,y⟩ = 0) :
    (realSchurMixedOrbitMatrix s T).BlockTriangular
      (fun p => realSchurLowerKey p.1) := by
  intro p q hqp
  rcases realSchurLower_lt_cases q.1 p.1 hqp with hfar | ⟨hdist,hneq⟩
  · exact realSchurMixedOrbitMatrix_distance_support s T hT p.1 q.1 p.2 q.2 hfar
  · exact realSchurMixedOrbitMatrix_same_distance_offdiagonal
      s T hT p.1 q.1 p.2 q.2 hdist hneq

#print axioms realSchurMixedOrbitMatrix_blockTriangular
end SpectralRadiusUpperTail
