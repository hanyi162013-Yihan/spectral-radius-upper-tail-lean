import SpectralRadiusUpperTail.IncrementMartingale
import Mathlib.Logic.Equiv.Fin.Basic

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped MeasureTheory
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {M N : ℕ}

/-- Serialize an actual finite array of differences in row-major order,
with zero increments after the last coordinate, also covering empty arrays. -/
noncomputable def finiteArrayIncrement (d : Fin M → Fin N → Ω → E) (r : ℕ) : Ω → E :=
  if h : r < M*N then
    let ij := finProdFinEquiv.symm (⟨r,h⟩ : Fin (M*N))
    d ij.1 ij.2
  else 0

lemma finiteArray_index_time (r : ℕ) (h : r < M*N) :
    (finProdFinEquiv.symm (⟨r,h⟩ : Fin (M*N))).1.val*N+
      (finProdFinEquiv.symm (⟨r,h⟩ : Fin (M*N))).2.val = r := by
  have he := congrArg Fin.val (finProdFinEquiv.apply_symm_apply (⟨r,h⟩ : Fin (M*N)))
  change (finProdFinEquiv.symm (⟨r,h⟩ : Fin (M*N))).2.val+
    N*(finProdFinEquiv.symm (⟨r,h⟩ : Fin (M*N))).1.val = r at he
  simpa only [Nat.mul_comm, Nat.add_comm] using he

lemma finiteArrayIncrement_at (d : Fin M → Fin N → Ω → E) (i : Fin M) (j : Fin N) :
    finiteArrayIncrement d (i.val*N+j.val) = d i j := by
  have h : i.val*N+j.val < M*N := by
    have := (finProdFinEquiv (i,j)).isLt
    change j.val+N*i.val < M*N at this
    simpa only [Nat.mul_comm, Nat.add_comm] using this
  rw [finiteArrayIncrement, dif_pos h]
  have he : (⟨i.val*N+j.val,h⟩ : Fin (M*N)) = finProdFinEquiv (i,j) := by
    apply Fin.ext
    change i.val*N+j.val = j.val+N*i.val
    ac_rfl
  rw [he, Equiv.symm_apply_apply]

/-- Integrability, next-time adaptation and conditional centering of the
actual coordinate differences give a matrix-valued martingale after serialization. -/
theorem martingale_finiteArrayIncrement (P : Measure Ω) [IsFiniteMeasure P]
    (F : Filtration ℕ mΩ) (d : Fin M → Fin N → Ω → E)
    (hd : ∀ i j, StronglyMeasurable[F (i.val*N+j.val+1)] (d i j))
    (hi : ∀ i j, Integrable (d i j) P)
    (hz : ∀ i j, P[d i j | F (i.val*N+j.val)] =ᵐ[P] 0) :
    Martingale (incrementPartialSum (finiteArrayIncrement d)) F P := by
  apply martingale_incrementPartialSum
  · intro r
    by_cases hr : r < M*N
    · rw [finiteArrayIncrement, dif_pos hr]
      have hh := hd (finProdFinEquiv.symm (⟨r,hr⟩ : Fin (M*N))).1
        (finProdFinEquiv.symm (⟨r,hr⟩ : Fin (M*N))).2
      rwa [finiteArray_index_time] at hh
    · rw [finiteArrayIncrement, dif_neg hr]
      exact stronglyMeasurable_zero
  · intro r
    by_cases hr : r < M*N
    · rw [finiteArrayIncrement, dif_pos hr]
      exact hi _ _
    · rw [finiteArrayIncrement, dif_neg hr]
      exact integrable_zero _ _ _
  · intro r
    by_cases hr : r < M*N
    · rw [finiteArrayIncrement, dif_pos hr]
      have hh := hz (finProdFinEquiv.symm (⟨r,hr⟩ : Fin (M*N))).1
        (finProdFinEquiv.symm (⟨r,hr⟩ : Fin (M*N))).2
      rwa [finiteArray_index_time] at hh
    · rw [finiteArrayIncrement, dif_neg hr, condExp_zero]

#print axioms martingale_finiteArrayIncrement
end SpectralRadiusUpperTail
