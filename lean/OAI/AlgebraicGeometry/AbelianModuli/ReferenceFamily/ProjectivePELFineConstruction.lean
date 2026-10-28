import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.ActionUnramified
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FieldPrescribedPELFine
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.QuasiProjectiveAmpleness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.QuasiProjectivePresentation

/-! # Projective PEL Fine Construction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectivePELFineConstruction

noncomputable section

/-! A quasi-projective pure fine moduli scheme gives a quasi-projective
fine scheme for the original integral PEL problem. The constructed
parameter of endomorphism actions is separated and quasi-finite; its
pulled-back ample bundle retains the actual projective geometry. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem quasiProjective_of_separated_quasiFinite
    {B : Scheme.{0}} [IsAffine B] [IsNoetherian B]
    {Y : Over B} (Q : HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation Y) (Z : Over Y.left)
    [LocallyOfFiniteType Z.hom] [LocallyQuasiFinite Z.hom]
    [IsSeparated Z.hom] [QuasiCompact Z.hom] :
    Nonempty (HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation ((Over.map Y.hom).obj Z)) := by
  have : LocallyOfFiniteType Y.hom := Q.locallyFiniteType
  have : IsSeparated Y.hom := Q.separated
  have : Y.left.IsSeparated := ⟨by
    rw [← terminal.comp_from Y.hom]
    infer_instance⟩
  have : Z.left.IsSeparated := ⟨by
    rw [← terminal.comp_from Z.hom]
    infer_instance⟩
  have hL := AmpleQuasiFinitePullback.ample_pullback_separated_quasiFinite Z.hom
    (QuasiProjectiveAmpleness.quasiProjectiveAmpleLineBundle Q) (QuasiProjectiveAmpleness.quasiProjectiveAmpleLineBundle_isAmple Q)
  exact hL.exists_quasiProjectivePresentation (Z.hom ≫ Y.hom)

/-- This is the unchanged all-test-schemes PEL functor, represented by
the actual action parameter over a pure fine moduli scheme. -/
theorem exists_quasiProjective_fine_pel_model_of_fine_pure
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} (P : Datum.RankThreePELDatum E s) (iota : E →+* K)
    (M : Pure.Fine.PurePolarizedModel (3 * s) P.polarizationType N (Spec (.of K)))
    (Q : HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation M.space) (hM : M.IsFine) (hN : 3 ≤ N) :
    ∃ F : Models.FinePELModel P iota N,
      F.IsFine ∧ Nonempty (HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation F.space) := by
  have : Countable K := NumberFieldCountability.numberField_countable K
  have : IsNoetherian M.space.left := Q.noetherian
  have : LocallyOfFiniteType M.space.hom := Q.locallyFiniteType
  let iotaO := iota.comp (algebraMap (NumberField.RingOfIntegers E) E)
  obtain ⟨Z, hn, hft, hqc, hsep, _, hqf, u, hclass⟩ :=
    PEL.ActionUnramified.exists_field_unramified_relative_pel_action_representation P iotaO M.space M.universal
  let V := (Over.map M.space.hom).obj Z
  have : LocallyOfFiniteType Z.hom := hft
  have : QuasiCompact Z.hom := hqc
  have : IsSeparated Z.hom := hsep
  have : LocallyQuasiFinite Z.hom := hqf
  let U := PELModuli.IntegralModel.Relative.FamilyClassification.relativePELUniversal P iotaO M.space M.universal Z u
  have hc := Relative.PELParameterClassification.relativePELParameter_classifies P iotaO M hM hN u hclass
  refine ⟨⟨V, U.toCharacteristicZero⟩, ?_, quasiProjective_of_separated_quasiFinite Q Z⟩
  intro T B
  obtain ⟨f, ⟨e⟩, hf⟩ := hc T (PELModuli.IntegralModel.PEL.BaseChange.integralPELOfCharacteristicZero B)
  refine ⟨f, ⟨FieldPrescribedPELFine.nativePELPullbackIso_of_integralComparison U B f e⟩, ?_⟩
  rintro k ⟨a⟩
  exact hf k ⟨FieldPrescribedPELFine.integralComparison_of_nativePELPullbackIso U B k a⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectivePELFineConstruction
