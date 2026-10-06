import SpectralRadiusUpperTail.RealSchurMixedDiagonalPolynomialStability
import SpectralRadiusUpperTail.RealSchurMixedFlagUnique
import SpectralRadiusUpperTail.RealSchurMixedRegularGaussianIntegration

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- In a neighborhood of a regular Schur representation, all matrices
with its global characteristic polynomial admit the same ordered block
polynomials. The finite-divisor argument fixes the spectral assignment. -/
theorem realSchurMixed_isospectral_local_representation
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : realSchurMixedLowerProjection s T=0)
    (hreg : (realSchurMixedOrbitMatrix s T).det ≠ 0)
    (Q : RealSchurMixedOrthogonalFrame s) :
    ∃ V : Set (Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ),
      IsOpen V ∧ Q.val*T*Q.valᵀ ∈ V ∧
      ∀ A ∈ V, A.charpoly=T.charpoly →
        ∃ P : RealSchurMixedOrthogonalFrame s,
          ∃ U : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ,
            realSchurMixedLowerProjection s U=0 ∧
            (∀ a, (realSchurMixedDiagonalMatrix s U a).charpoly =
              (realSchurMixedDiagonalMatrix s T a).charpoly) ∧ A=P.val*U*P.valᵀ := by
  obtain ⟨W,hWo,hTW,hWeq⟩ := exists_open_realSchurMixed_diagonal_polynomial_stability s hs T
  let C := (realSchurMixedRegularRotatedChart s T hreg Q.val Q.property).restrOpen
    ((fun x : RealSchurMixedTangent s => T+x.2.val) ⁻¹' W)
    (hWo.preimage (continuous_const.add (realSchurMixedUpperTangentCLM s).continuous))
  have hzero : (0 : RealSchurMixedTangent s) ∈ C.source := by
    refine ⟨realSchurMixedRegularChart_zero_mem_source s T hreg, ?_⟩
    change T+0 ∈ W
    simpa only [add_zero] using hTW
  have happly (x : RealSchurMixedTangent s) :
      C x=Q.val*(realSchurMixedExpCoordinates s T x)*Q.valᵀ := rfl
  have hcenter : Q.val*T*Q.valᵀ ∈ C.target := by
    have h := C.map_source hzero
    simpa only [happly,realSchurMixedExpCoordinates_zero] using h
  refine ⟨C.target,C.open_target,hcenter,?_⟩
  intro A hA hpoly
  let x := C.symm A
  have hx : x ∈ C.source := C.map_target hA
  have hmap : C x=A := C.right_inv hA
  let P : RealSchurMixedOrthogonalFrame s :=
    ⟨Q.val*realSchurMixedAngularFrame s x.1, realSchurMixed_rotatedFrame_orthogonal s Q x.1⟩
  let U := T+x.2.val
  have hrep : A=P.val*U*P.valᵀ := by
    rw [← hmap,happly,realSchurMixedExpCoordinates_eq_conjugation]
    simp only [P,U,Matrix.transpose_mul,Matrix.mul_assoc]
  have hLower : realSchurMixedLowerProjection s U=0 := by
    dsimp only [U]
    rw [map_add,hT,zero_add]
    exact x.2.property
  have hUpoly : U.charpoly=T.charpoly := by
    rw [hrep,realMatrixOrthogonalConjugation_charpoly _ _ _ P.property] at hpoly
    exact hpoly
  exact ⟨P,U,hLower,hWeq U hx.2 hLower hUpoly,hrep⟩

#print axioms realSchurMixed_isospectral_local_representation
end SpectralRadiusUpperTail
