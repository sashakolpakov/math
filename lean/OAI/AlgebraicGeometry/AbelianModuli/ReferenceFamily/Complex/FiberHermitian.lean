import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.EmbeddingRanks
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianNormalizer
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianNondegenerate
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DefiniteAnisotropy

/-! # Fiber Hermitian -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Every actual complex PEL fiber has a reconstructed nondegenerate
Hermitian matrix, with the prescribed distinguished normalizer and
definite compact embedding blocks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ}
    {P : Datum.RankThreePELDatum E s} {iota : E →+* K} {T : Over (Spec (.of K))}

def Datum.RankThreePELDatum.normalizedImaginaryScalar (P : Datum.RankThreePELDatum E s) : E :=
  ImaginaryHermitianWeights.positiveImaginaryScalar (P.embeddings P.distinguished) P.imaginaryScalar

theorem Datum.RankThreePELDatum.normalizedImaginaryScalar_spec (hP : P.IsAdmissible) :
    P.normalizedImaginaryScalar ≠ 0 ∧
      ComplexMultiplication.CM.TraceForm.cmFieldConjugation E P.normalizedImaginaryScalar = -P.normalizedImaginaryScalar ∧
      0 < (P.μ P.normalizedImaginaryScalar).im :=
  ImaginaryHermitianWeights.positiveImaginaryScalar_spec (P.embeddings P.distinguished) P.imaginaryScalar
    hP.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.1

variable (A : PEL.Objects.PELObject P iota N T) (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (p : Spec (.of ℂ) ⟶ T.left)

def PEL.Objects.PELObject.complexFiberHermitianMatrix : Matrix (Fin 3) (Fin 3) E :=
  Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix (A.polarized.pullback p) (A.action.pullback p) s hs rfl hdegree
    (ActionData.RosatiConjugation.pullback A.polarized A.action A.rosati p) P.normalizedImaginaryScalar

theorem PEL.Objects.PELObject.complexFiberHermitianMatrix_symmetry (hP : P.IsAdmissible) (i j : Fin 3) :
    A.complexFiberHermitianMatrix hs hdegree p i j =
      ComplexMultiplication.CM.TraceForm.cmFieldConjugation E (A.complexFiberHermitianMatrix hs hdegree p j i) :=
  Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix_symmetry (A.polarized.pullback p) (A.action.pullback p) s hs rfl hdegree
    (ActionData.RosatiConjugation.pullback A.polarized A.action A.rosati p) P.normalizedImaginaryScalar
    (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).2.1 i j

theorem PEL.Objects.PELObject.complexFiberHermitianMatrix_det_ne_zero (hP : P.IsAdmissible) :
    (A.complexFiberHermitianMatrix hs hdegree p).det ≠ 0 :=
  Intrinsic.HermitianNondegenerate.IntrinsicHermitianMarking.markedHermitianMatrix_det_ne_zero (A.polarized.pullback p) (A.action.pullback p) s hs rfl hdegree
    (ActionData.RosatiConjugation.pullback A.polarized A.action A.rosati p) P.normalizedImaginaryScalar
    (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).1

variable [IsGalois ℚ E] (κ : K →+* ℂ) (hκ : κ.comp iota = P.μ)
    (hp : p ≫ T.hom = Spec.map (CommRingCat.ofHom κ))

include hκ hp in
theorem PEL.Objects.PELObject.complexFiberHermitianMatrix_normalizer (hP : P.IsAdmissible) :
    ∃ e : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ), ∀ x y,
      Datum.RankThreePELDatum.complexMatrixHermitian P.μ (A.complexFiberHermitianMatrix hs hdegree p) (e x) (e y) =
        Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y := by
  obtain ⟨hξ, hc, hi⟩ := Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP
  exact Intrinsic.HermitianNormalizer.IntrinsicHermitianMarking.exists_nativeHermitian_normalizer (A.polarized.pullback p) (A.action.pullback p) s hs rfl hdegree
    (P.embeddings P.distinguished) (ActionData.RosatiConjugation.pullback A.polarized A.action A.rosati p)
    P.normalizedImaginaryScalar hξ hc hi (A.complexFiber_distinguished_rank κ hκ p hp hP)
    P.b hP.2.1 hP.2.2.2.1

include hκ hp in
theorem PEL.Objects.PELObject.complexFiberHermitianMatrix_compact (hP : P.IsAdmissible)
    (i : Fin s) (hi : i ≠ P.distinguished) :
    (∀ x : Fin 3 → ℂ, x ≠ 0 →
      0 < (Datum.RankThreePELDatum.complexMatrixHermitian (P.embeddings i).toRingHom
        (A.complexFiberHermitianMatrix hs hdegree p) x x).re) ∨
    (∀ x : Fin 3 → ℂ, x ≠ 0 →
      (Datum.RankThreePELDatum.complexMatrixHermitian (P.embeddings i).toRingHom
        (A.complexFiberHermitianMatrix hs hdegree p) x x).re < 0) := by
  have hextreme : P.firstLieRank i = 0 ∨ P.firstLieRank i = 3 := by
    unfold Datum.RankThreePELDatum.firstLieRank
    rw [ite_eq_right hi]
    split <;> simp
  exact Intrinsic.CompactHermitian.IntrinsicHermitianMarking.nativeHermitianMatrix_definite_of_LieRank (A.polarized.pullback p) (A.action.pullback p)
    s hs rfl hdegree (P.embeddings i) (ActionData.RosatiConjugation.pullback A.polarized A.action A.rosati p)
    P.normalizedImaginaryScalar (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).1
    (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).2.1
    (A.complexFiber_embedding_rank κ hκ p hp hP i) hextreme

include hκ hp in
theorem PEL.Objects.PELObject.complexFiberHermitianMatrix_anisotropic (hP : P.IsAdmissible) (hs' : 1 < s) :
    ∀ x : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, Datum.RankThreePELDatum.matrixHermitian (A.complexFiberHermitianMatrix hs hdegree p) x x = 0 →
      x = 0 := by
  let : Nontrivial (Fin s) := Fin.nontrivial_iff_two_le.mpr hs'
  obtain ⟨i, hi⟩ := exists_ne P.distinguished
  exact DefiniteAnisotropy.matrixHermitian_anisotropic_of_definite (P.embeddings i) _
    (A.complexFiberHermitianMatrix_compact hs hdegree p κ hκ hp hP i hi)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
