import SpectralRadiusUpperTail.RealSchurGlobalModel
import SpectralRadiusUpperTail.GaussianChainMoment
import SpectralRadiusUpperTail.MatrixChainScaling
import SpectralRadiusUpperTail.MatrixSquareIntegrability
import SpectralRadiusUpperTail.FiniteSumCrossOrthogonality

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma realSchurGlobalWaitingSum_eq {N : ℕ} (n k : ℕ) (B : Fin N → RealSchurBlockData)
    (p : AnyIncreasingPath N) (s : Fin N → ℝ) (x : SchurEntryIndex N 2 → ℝ) :
    realSchurGlobalWaitingSum n k B p (s,x) =
      ∑ m : SchurWaitingTimes k p.1, (1/Real.sqrt n)^p.1 • schurPathMatrix p
        (fun i => realSchurDataPower (B (p.2.val i)) (m.val i) (s (p.2.val i))) x := by
  unfold realSchurGlobalWaitingSum realSchurWaitingSum realSchurPathProduct realSchurSelectPath
  simp only [gaussianBridgeProduct_fromArray, matrixChain_scale_random]
  rfl

lemma realSchurGlobalWaitingSum_entry_measurable {N : ℕ} (n k : ℕ) (hn : 0 < n)
    (B : Fin N → RealSchurBlockData) (hB : ∀ i, realSchurDataAdmissible (B i))
    (p : AnyIncreasingPath N) (a b : Fin 2) :
    Measurable (fun z => realSchurGlobalWaitingSum n k B p z a b) := by
  have hp := (realSchurSelectPath_measurePreserving n hn B hB p).measurable
  unfold realSchurGlobalWaitingSum realSchurWaitingSum
  simp only [Matrix.sum_apply]
  apply Finset.measurable_sum
  intro m _
  exact (realSchurPathProduct_entry_measurable n p.1 (fun i => B (p.2.val i))
    (fun i => hB (p.2.val i)) m.val a b).comp hp

/-- Orthogonality after fixing the entire diagonal array. The two waiting
sums use the same Gaussian blocks and may share any number of vertices. -/
lemma real_schur_waiting_conditional_cross_zero {N : ℕ} (n k : ℕ)
    (B : Fin N → RealSchurBlockData) (p q : AnyIncreasingPath N)
    (hlast : anyPathLast p = anyPathLast q) (hne : p ≠ q)
    (s : Fin N → ℝ) (a b : Fin 2) :
    (∫ x : SchurEntryIndex N 2 → ℝ, realSchurGlobalWaitingSum n k B p (s,x) a b *
      realSchurGlobalWaitingSum n k B q (s,x) a b ∂Measure.pi (fun _ => standardNormal)) = 0 := by
  simp only [realSchurGlobalWaitingSum_eq, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply (finite_sum_cross_orthogonality (Measure.pi (fun _ => standardNormal)) _ _ ?_ ?_).2
  · intro m v
    have hi := (schurPathMatrix_pair_integrable p q
      (fun i => realSchurDataPower (B (p.2.val i)) (m.val i) (s (p.2.val i)))
      (fun i => realSchurDataPower (B (q.2.val i)) (v.val i) (s (q.2.val i))) a b a b).const_mul
      ((1/Real.sqrt n)^p.1*(1/Real.sqrt n)^q.1)
    exact hi.congr (Filter.Eventually.of_forall (fun x => by ring))
  · intro m v
    have he (x : SchurEntryIndex N 2 → ℝ) :
        ((1/Real.sqrt n)^p.1 * schurPathMatrix p
          (fun i => realSchurDataPower (B (p.2.val i)) (m.val i) (s (p.2.val i))) x a b) *
        ((1/Real.sqrt n)^q.1 * schurPathMatrix q
          (fun i => realSchurDataPower (B (q.2.val i)) (v.val i) (s (q.2.val i))) x a b) =
        ((1/Real.sqrt n)^p.1*(1/Real.sqrt n)^q.1) *
        (schurPathMatrix p (fun i => realSchurDataPower (B (p.2.val i)) (m.val i) (s (p.2.val i))) x a b *
         schurPathMatrix q (fun i => realSchurDataPower (B (q.2.val i)) (v.val i) (s (q.2.val i))) x a b) := by ring
    simp_rw [he]
    rw [integral_const_mul, schurPathMatrix_cross_zero p q hlast hne, mul_zero]

/-- Conditional orthogonality survives integration over the random diagonal blocks. -/
lemma real_schur_global_waiting_cross_zero {N : ℕ} (n k : ℕ) (hn : 0 < n)
    (η ρ : ℝ) (hη : 0 < η) (B : Fin N → RealSchurBlockData)
    (hB : ∀ i, realSchurDataAdmissible (B i)) (hmod : ∀ i, realSchurDataRadius (B i) ≤ ρ)
    (p q : AnyIncreasingPath N) (hpk : p.1 ≤ k) (hqk : q.1 ≤ k)
    (hlast : anyPathLast p = anyPathLast q) (hne : p ≠ q) (a b : Fin 2) :
    (∫ z, realSchurGlobalWaitingSum n k B p z a b * realSchurGlobalWaitingSum n k B q z a b
      ∂realSchurGlobalLaw n B) = 0 := by
  haveI (i : Fin N) := realSchurDataLaw_probability (n : ℝ) (Nat.cast_pos.mpr hn) (B i) (hB i)
  have hi := matrix_entry_pair_integrable (realSchurGlobalLaw n B)
    (realSchurGlobalWaitingSum n k B p) (realSchurGlobalWaitingSum n k B q)
    (realSchurGlobalWaitingSum_entry_measurable n k hn B hB p)
    (realSchurGlobalWaitingSum_entry_measurable n k hn B hB q)
    (real_schur_global_waiting_second_moment n k hn η ρ hη B hB hmod p hpk).1
    (real_schur_global_waiting_second_moment n k hn η ρ hη B hB hmod q hqk).1 a b
  change (∫ z, realSchurGlobalWaitingSum n k B p z a b * realSchurGlobalWaitingSum n k B q z a b
    ∂(Measure.pi (fun i => realSchurDataLaw n (B i))).prod (Measure.pi (fun _ => standardNormal))) = 0
  rw [integral_prod _ hi]
  simp_rw [real_schur_waiting_conditional_cross_zero n k B p q hlast hne]
  simp

#print axioms real_schur_waiting_conditional_cross_zero
#print axioms real_schur_global_waiting_cross_zero
end SpectralRadiusUpperTail
