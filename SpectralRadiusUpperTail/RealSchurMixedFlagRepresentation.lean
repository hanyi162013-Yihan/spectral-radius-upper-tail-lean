import SpectralRadiusUpperTail.RealSchurMixedFlagPatches
import SpectralRadiusUpperTail.RealBlockDiagonalConjugation

namespace SpectralRadiusUpperTail
open scoped Matrix Matrix.Norms.Operator

/-- Every orthogonal block-upper representation can be moved into one
selected angle patch. Only an orthogonal change inside each diagonal
block is used, so upper triangularity and all ordered block spectra are
preserved. There is no restriction on the strict-upper entries. -/
theorem realSchurMixedFlag_representation_coverage
    {m : ℕ} (s : Fin m → ℕ) (hs : ∀ i, 0 < s i)
    (c : Fin m → ℝ) (hc : Function.Injective c)
    (R : ℕ → RealSchurMixedOrthogonalFrame s)
    (hcover : ∀ Q : RealSchurMixedOrthogonalFrame s, ∃ k,
      Q.val*realSchurMixedBlockScalar s c*Q.valᵀ ∈
        (realSchurMixedMarkerRotatedChart s hs c hc (R k).val (R k).property).target)
    (Q : RealSchurMixedOrthogonalFrame s)
    (T : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ)
    (hT : T.BlockTriangular (fun i : RealSchurMixedCoord s => i.1)) :
    ∃ k, ∃ w ∈ realSchurMixedFlagAnglePatch s hs c hc R k,
      ∃ U : Matrix (RealSchurMixedCoord s) (RealSchurMixedCoord s) ℝ,
        U.BlockTriangular (fun i : RealSchurMixedCoord s => i.1) ∧
        (∀ a, (U.toSquareBlock (fun i : RealSchurMixedCoord s => i.1) a).charpoly =
          (T.toSquareBlock (fun i : RealSchurMixedCoord s => i.1) a).charpoly) ∧
        Q.val*T*Q.valᵀ =
          ((R k).val*realSchurMixedAngularFrame s w)*U*
            ((R k).val*realSchurMixedAngularFrame s w)ᵀ := by
  let D := realSchurMixedBlockScalar s c
  obtain ⟨k,hk⟩ := exists_realSchurMixedFlagMarkerPatch s hs c hc R hcover Q
  have htarget : Q.val*D*Q.valᵀ ∈
      (realSchurMixedMarkerRotatedChart s hs c hc (R k).val (R k).property).target :=
    disjointed_subset _ k hk
  have hD : D.IsHermitian := Matrix.isHermitian_diagonal _
  have hHerm : (Q.val*D*Q.valᵀ).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_mul_mul_conjTranspose Q.val hD
  have hpoly : (Q.val*D*Q.valᵀ).charpoly = D.charpoly :=
    realMatrixOrthogonalConjugation_charpoly _ Q.val D Q.property
  obtain ⟨w,hw,hmark⟩ := realSchurMixedFlagMarker_rotated_coverage
    s hs c hc (R k).val (R k).property _ htarget hHerm hpoly
  have hpatch : w ∈ realSchurMixedFlagAnglePatch s hs c hc R k := by
    refine ⟨hw,?_⟩
    change (R k).val*realSchurMixedFlagMarker s c w*(R k).valᵀ ∈
      realSchurMixedFlagMarkerPatch s hs c hc R k
    rw [hmark]
    exact hk
  let P := (R k).val*realSchurMixedAngularFrame s w
  have hP : Pᵀ*P=1 := by
    dsimp only [P]
    rw [Matrix.transpose_mul]
    calc
      _ = (realSchurMixedAngularFrame s w)ᵀ*((R k).valᵀ*(R k).val)*
          realSchurMixedAngularFrame s w := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [(R k).property, Matrix.mul_one, realSchurMixedAngularFrame_orthogonal]
  have hmarker : realSchurBlockMarker (fun i : RealSchurMixedCoord s => i.1) c P =
      realSchurBlockMarker (fun i : RealSchurMixedCoord s => i.1) c Q.val := by
    simpa only [P, D, realSchurMixedFlagMarker, realSchurBlockMarker,
      realSchurMixedBlockScalar, Matrix.transpose_mul, Matrix.mul_assoc] using hmark
  let W := Pᵀ*Q.val
  have hW : Wᵀ*W=1 := by
    dsimp only [W]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      _ = Q.valᵀ*(P*Pᵀ)*Q.val := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [mul_eq_one_comm.mp hP, Matrix.mul_one, Q.property]
  have hoff : ∀ i j : RealSchurMixedCoord s, i.1 ≠ j.1 → W i j = 0 :=
    realSchurBlockMarker_offBlock_of_eq (fun i : RealSchurMixedCoord s => i.1)
      c hc P Q.val hP Q.property hmarker
  let U := W*T*Wᵀ
  obtain ⟨hU,hdiag⟩ := blockDiagonal_orthogonal_conjugation
    (fun i : RealSchurMixedCoord s => i.1) W T hW hoff hT
  refine ⟨k,w,hpatch,U,hU,hdiag,?_⟩
  have hPW : P*W=Q.val := by
    dsimp only [W]
    rw [← Matrix.mul_assoc, mul_eq_one_comm.mp hP, Matrix.one_mul]
  change Q.val*T*Q.valᵀ = P*U*Pᵀ
  calc
    _ = (P*W)*T*(P*W)ᵀ := by rw [hPW]
    _ = _ := by dsimp only [U]; rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]

#print axioms realSchurMixedFlag_representation_coverage
end SpectralRadiusUpperTail
