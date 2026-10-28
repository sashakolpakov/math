import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ArchFrame

/-! # Global Frame -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.GlobalFrame

noncomputable section

/-! Assemble the actual native frame action over every archimedean place.
All compact blocks have determinant one; the active block supplies the
square of the projective denominator. -/

open scoped Classical _root_.Matrix

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (v : Multiplicity.Odd.Sign E)

def nativeFramePlaceMatrix (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (τ : Fin s) : Matrix (Fin 3) (Fin 3) ℂ :=
  if τ = P.distinguished then ArchFrame.nativeActiveFrameMatrix E P g z
  else if Multiplicity.Period.nativeCompactSigns E P v τ then (ArchFrame.archConjugateUnitaryBlock E P τ g).val
  else (ArchFrame.archUnitaryBlock E P τ g).val

def nativeGlobalFrameMatrix (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) :
    Matrix (Fin s × Fin 3) (Fin s × Fin 3) ℂ :=
  Matrix.reindexRingEquiv ℂ (Equiv.prodComm (Fin 3) (Fin s))
    (Matrix.blockDiagonal (nativeFramePlaceMatrix E P v g z))

theorem nativeGlobalFrameMatrix_entry (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (τ υ : Fin s) (i j : Fin 3) :
    nativeGlobalFrameMatrix E P v g z (τ, i) (υ, j) =
      if τ = υ then nativeFramePlaceMatrix E P v g z τ i j else 0 := rfl

theorem nativeGlobalFrameMatrix_mulVec (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (x : Fin s × Fin 3 → ℂ) (τ : Fin s) (i : Fin 3) :
    (nativeGlobalFrameMatrix E P v g z *ᵥ x) (τ, i) =
      (nativeFramePlaceMatrix E P v g z τ *ᵥ (fun j => x (τ, j))) i := by
  change (∑ j, nativeGlobalFrameMatrix E P v g z (τ, i) j * x j) = _
  simp [Fintype.sum_prod_type, nativeGlobalFrameMatrix_entry, Matrix.mulVec, dotProduct]

theorem nativeFramePlaceMatrix_compact_det (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (τ : Fin s) (hτ : τ ≠ P.distinguished) :
    (nativeFramePlaceMatrix E P v g z τ).det = 1 := by
  unfold nativeFramePlaceMatrix
  rw [ite_eq_right hτ]
  split_ifs
  · exact (ArchFrame.archConjugateUnitaryBlock E P τ g).property
  · exact (ArchFrame.archUnitaryBlock E P τ g).property

theorem nativeGlobalFrameMatrix_det (hP : P.IsAdmissible)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) :
    (nativeGlobalFrameMatrix E P v g z).det =
      RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator (ArchFrame.archUnitaryBlock E P P.distinguished g) z ^ 2 := by
  change (Matrix.reindex (Equiv.prodComm (Fin 3) (Fin s)) (Equiv.prodComm (Fin 3) (Fin s))
    (Matrix.blockDiagonal (nativeFramePlaceMatrix E P v g z))).det = _
  rw [Matrix.det_reindex_self, Matrix.det_blockDiagonal,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ P.distinguished)]
  have hp : ∏ τ ∈ Finset.univ.erase P.distinguished, (nativeFramePlaceMatrix E P v g z τ).det = 1 :=
    Finset.prod_eq_one fun τ hτ => nativeFramePlaceMatrix_compact_det E P v g z τ
      (Finset.mem_erase.mp hτ).1
  rw [hp, mul_one]
  change (if P.distinguished = P.distinguished then ArchFrame.nativeActiveFrameMatrix E P g z else _).det = _
  rw [ite_eq_left rfl]
  exact ArchFrame.nativeActiveFrameMatrix_det E P hP g z

theorem native_place_frame_transform (hP : P.IsAdmissible)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (hz : z ∈ P.domain)
    (τ : Fin s) (u : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    ((ArchFrame.archUnitaryBlock E P τ g).val.mulVec
        (Geometry.ComplexBall.PrescribedSignsB.placeFrame (Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Multiplicity.nativeMatrix E P)) P.distinguished (Multiplicity.Period.nativeCompactSigns E P v) z τ u).1,
      (ArchFrame.archConjugateUnitaryBlock E P τ g).val.mulVec
        (Geometry.ComplexBall.PrescribedSignsB.placeFrame (Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Multiplicity.nativeMatrix E P)) P.distinguished (Multiplicity.Period.nativeCompactSigns E P v) z τ u).2) =
      Geometry.ComplexBall.PrescribedSignsB.placeFrame (Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Multiplicity.nativeMatrix E P)) P.distinguished (Multiplicity.Period.nativeCompactSigns E P v)
        (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ g z) τ (nativeFramePlaceMatrix E P v g z τ *ᵥ u) := by
  by_cases hτ : τ = P.distinguished
  · subst τ
    simpa [Geometry.ComplexBall.PrescribedSignsB.placeFrame, nativeFramePlaceMatrix] using
      ArchFrame.native_active_frame_transform E P hP g z hz u
  · cases hd : Multiplicity.Period.nativeCompactSigns E P v τ <;>
      simp [Geometry.ComplexBall.PrescribedSignsB.placeFrame, nativeFramePlaceMatrix, hτ, hd]

theorem native_global_frame_transform (hP : P.IsAdmissible)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (hz : z ∈ P.domain)
    (u : Fin s × Fin 3 → ℂ) :
    ArchUnitaryCoordinates.Intrinsic.pairedUnitaryEnd E P g
        (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.flatFrame (Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Multiplicity.nativeMatrix E P)) P.distinguished (Multiplicity.Period.nativeCompactSigns E P v) z u) =
      RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.flatFrame (Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Multiplicity.nativeMatrix E P)) P.distinguished (Multiplicity.Period.nativeCompactSigns E P v)
        (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ g z) (nativeGlobalFrameMatrix E P v g z *ᵥ u) := by
  funext τ
  have h := native_place_frame_transform E P v hP g z hz τ (fun i => u (τ, i))
  have he : (fun i => (nativeGlobalFrameMatrix E P v g z *ᵥ u) (τ, i)) =
      nativeFramePlaceMatrix E P v g z τ *ᵥ (fun i => u (τ, i)) :=
    funext (nativeGlobalFrameMatrix_mulVec E P v g z u τ)
  change _ = Geometry.ComplexBall.PrescribedSignsB.placeFrame (Geometry.ComplexBall.PrescribedSignsB.matrixB P.embeddings (Multiplicity.nativeMatrix E P)) P.distinguished (Multiplicity.Period.nativeCompactSigns E P v)
    (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ g z) τ (fun i => (nativeGlobalFrameMatrix E P v g z *ᵥ u) (τ, i))
  rw [he]
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.GlobalFrame
