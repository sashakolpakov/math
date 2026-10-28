import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.FiberHermitian
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieTransport
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Classifying

/-! # Hermitian Arithmetic -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.HermitianArithmetic.PELObject

noncomputable section

/-! Compact-place definiteness and anisotropy of the Hermitian matrix
on the original object's own period marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [IsGalois ℚ E] [Field K] {s N : ℕ} {P : Datum.RankThreePELDatum E s}
    {iota : E →+* K} {κ : K →+* ℂ}
    (A : PEL.Objects.PELObject P iota N (Over.mk (Spec.map (CommRingCat.ofHom κ))))
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)

local notation "H" => OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HermitianMarking.IntrinsicHermitianMarking.markedHermitianMatrix A.polarized A.action s hs rfl hdegree
  A.rosati P.normalizedImaginaryScalar

include hP hκ in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Objects.PELObject.originalHermitianMatrix_compact (i : Fin s) (hi : i ≠ P.distinguished) :
    (∀ x : Fin 3 → ℂ, x ≠ 0 →
      0 < (Datum.RankThreePELDatum.complexMatrixHermitian (P.embeddings i).toRingHom H x x).re) ∨
    (∀ x : Fin 3 → ℂ, x ≠ 0 →
      (Datum.RankThreePELDatum.complexMatrixHermitian (P.embeddings i).toRingHom H x x).re < 0) := by
  have hr := A.complexFiber_embedding_rank κ hκ (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase) (Category.id_comp _) hP i
  have hr' : LieRanks.HasLieRank A.polarized.abelian A.action
      ((P.embeddings i).toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E))
      (P.firstLieRank i) :=
    LieTransport.hasLieRank_transport (A.action.pullback (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) A.action
      A.polarized.abelian.pullbackIdIso (PEL.Objects.PELIso.pullbackId A).action _ (P.firstLieRank i) hr
  have hextreme : P.firstLieRank i = 0 ∨ P.firstLieRank i = 3 := by
    unfold Datum.RankThreePELDatum.firstLieRank
    rw [ite_eq_right hi]
    split <;> simp
  exact Intrinsic.CompactHermitian.IntrinsicHermitianMarking.nativeHermitianMatrix_definite_of_LieRank A.polarized A.action s hs rfl hdegree
    (P.embeddings i) A.rosati P.normalizedImaginaryScalar
    (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).1
    (Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP).2.1 hr' hextreme

include hP hκ in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Objects.PELObject.originalHermitianMatrix_anisotropic (hs' : 1 < s) :
    ∀ x : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, Datum.RankThreePELDatum.matrixHermitian H x x = 0 → x = 0 := by
  let : Nontrivial (Fin s) := Fin.nontrivial_iff_two_le.mpr hs'
  obtain ⟨i, hi⟩ := exists_ne P.distinguished
  exact DefiniteAnisotropy.matrixHermitian_anisotropic_of_definite (P.embeddings i) H
    (A.originalHermitianMatrix_compact hs hdegree hP hκ i hi)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.HermitianArithmetic.PELObject
