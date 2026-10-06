import SpectralRadiusUpperTail.RealPairGapPowerMoment
import SpectralRadiusUpperTail.RealSchurMixedGaussianWeight

namespace SpectralRadiusUpperTail
open MeasureTheory
open scoped Matrix ENNReal BigOperators

def realPairGapSq (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (A 0 0-A 1 1)^2+(A 0 1+A 1 0)^2

theorem realPairGapSq_nonneg (A : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ realPairGapSq A :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem realPairGapSq_eq_energy_sub_det (A : Matrix (Fin 2) (Fin 2) ℝ) :
    realPairGapSq A=(∑ ij : Fin 2 × Fin 2, (A ij.1 ij.2)^2)-2*A.det := by
  simp [realPairGapSq,Fintype.sum_prod_type,Fin.sum_univ_two,Matrix.det_fin_two]
  ring

theorem realPairCenter_conjugation (Q A : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Qᵀ*Q=1) :
    realPairCenter (Q*A*Qᵀ)=realPairCenter A := by
  unfold realPairCenter
  rw [Matrix.trace_mul_cycle,hQ,Matrix.one_mul]

theorem realPairDet_conjugation (Q A : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Qᵀ*Q=1) :
    (Q*A*Qᵀ).det=A.det := by
  calc
    _ = (Qᵀ*Q).det*A.det := by simp only [Matrix.det_mul,Matrix.det_transpose]; ring
    _ = _ := by rw [hQ,Matrix.det_one,one_mul]

theorem realPairGapSq_conjugation (Q A : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Qᵀ*Q=1) :
    realPairGapSq (Q*A*Qᵀ)=realPairGapSq A := by
  have h := realMatrixGaussianWeight_orthogonal_conjugation (Fin 2) Q A hQ
  unfold realMatrixGaussianWeight at h
  have he : (∑ ij : Fin 2 × Fin 2, ((Q*A*Qᵀ) ij.1 ij.2)^2)=
      ∑ ij : Fin 2 × Fin 2, (A ij.1 ij.2)^2 := by
    have hh := Real.exp_injective h
    linarith
  rw [realPairGapSq_eq_energy_sub_det,realPairGapSq_eq_energy_sub_det,he,
    realPairDet_conjugation Q A hQ]

/-- Real part, squared imaginary part, and squared singular gap. -/
noncomputable def realPairSpectralGapCoordinates (a : (Fin 2 × Fin 2) → ℝ) : ℝ × (ℝ × ℝ) :=
  (realPairCenter (Matrix.of a.curry),realPairHeightSq (Matrix.of a.curry),realPairGapSq (Matrix.of a.curry))

theorem realPairSpectralGapCoordinates_measurable : Measurable realPairSpectralGapCoordinates := by
  unfold realPairSpectralGapCoordinates realPairHeightSq realPairCenter realPairGapSq
  simp only [Matrix.trace_fin_two,Matrix.det_fin_two]
  change Measurable (fun a : (Fin 2 × Fin 2) → ℝ =>
    ((a (0,0)+a (1,1))/2,
      a (0,0)*a (1,1)-a (0,1)*a (1,0)-((a (0,0)+a (1,1))/2)^2,
      (a (0,0)-a (1,1))^2+(a (0,1)+a (1,0))^2))
  fun_prop

theorem realPairSpectralGapCoordinates_conjugation
    (Q A : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Qᵀ*Q=1) :
    realPairSpectralGapCoordinates (fun ij => (Q*A*Qᵀ) ij.1 ij.2)=
      realPairSpectralGapCoordinates (fun ij => A ij.1 ij.2) := by
  change (realPairCenter (Q*A*Qᵀ),realPairHeightSq (Q*A*Qᵀ),realPairGapSq (Q*A*Qᵀ))=
    (realPairCenter A,realPairHeightSq A,realPairGapSq A)
  simp only [realPairHeightSq,realPairCenter_conjugation Q A hQ,
    realPairDet_conjugation Q A hQ,realPairGapSq_conjugation Q A hQ]

theorem realPairSpectralGapCoordinates_block (x b c : ℝ) :
    realPairSpectralGapCoordinates (fun ij => realSchurBlock x b c ij.1 ij.2)=
      (x,b*c,(b-c)^2) := by
  unfold realPairSpectralGapCoordinates realPairHeightSq realPairCenter realPairGapSq
  simp [realSchurBlock,Matrix.trace_fin_two,Matrix.det_fin_two]
  constructor <;> ring

theorem realPairSpectralGapCoordinates_cartesian (x a p q : ℝ) :
    realPairSpectralGapCoordinates (fun ij => realPairCartesianMatrix x a p q ij.1 ij.2)=
      (x,q^2-(a^2+p^2),4*(a^2+p^2)) := by
  change (realPairCenter (realPairCartesianMatrix x a p q),
    realPairHeightSq (realPairCartesianMatrix x a p q),realPairGapSq (realPairCartesianMatrix x a p q))=_
  rw [realPairCartesianMatrix_center,realPairCartesianMatrix_heightSq]
  simp [realPairGapSq,realPairCartesianMatrix]
  constructor <;> ring

theorem realPairSpectralGapCoordinates_gapBlock (x u s : ℝ) (hu : 0 < u) (hs : 0 < s) :
    realPairSpectralGapCoordinates (realPairGapBlockEntries x (u,s))=(x,u,s) := by
  change realPairSpectralGapCoordinates (fun ij => realSchurBlock x
    (realSchurPairFromCoordinates u s).1 (realSchurPairFromCoordinates u s).2 ij.1 ij.2)=(x,u,s)
  rw [realPairSpectralGapCoordinates_block]
  exact congrArg (fun p : ℝ × ℝ => (x,p)) (realSchur_pair_chart_forward u s hu hs)

#print axioms realPairGapSq_conjugation
#print axioms realPairSpectralGapCoordinates_measurable
#print axioms realPairSpectralGapCoordinates_conjugation
#print axioms realPairSpectralGapCoordinates_block
#print axioms realPairSpectralGapCoordinates_cartesian
#print axioms realPairSpectralGapCoordinates_gapBlock
end SpectralRadiusUpperTail
