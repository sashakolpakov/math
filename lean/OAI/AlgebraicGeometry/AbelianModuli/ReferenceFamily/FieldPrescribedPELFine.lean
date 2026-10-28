import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Relative.PELParameterClassification
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Classifying
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NumberFieldCountability

/-! # Field Prescribed PEL Fine -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FieldPrescribedPELFine

noncomputable section

/-! A fine prescribed-level pure model gives a fine model of the original
integral PEL problem, using the constructed all-test action parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.BaseChange

theorem exists_field_prescribed_pel_classifier
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [CharZero K] [Countable K] {s N : ℕ} (P : Datum.RankThreePELDatum E s)
    (iotaO : NumberField.RingOfIntegers E →+* K)
    (M : Pure.Fine.PurePolarizedModel (3 * s) P.polarizationType N (Spec (.of K)))
    [IsNoetherian M.space.left] [LocallyOfFiniteType M.space.hom] (hM : M.IsFine) (hN : 3 ≤ N) :
    ∃ V : Over (Spec (.of K)), IsNoetherian V.left ∧ LocallyOfFiniteType V.hom ∧
      ∃ U : PELModuli.IntegralModel.PEL.Has.IntegralPELObject P K iotaO N V,
        ∀ (T : Over (Spec (.of K))) (B : PELModuli.IntegralModel.PEL.Has.IntegralPELObject P K iotaO N T),
          ∃! f : T ⟶ V, Nonempty (PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso (U.data.pullback f.left) B.data) := by
  obtain ⟨Z, hn, hft, _, _, u, hclass⟩ := FieldRelativePELAction.exists_field_relative_pel_action_representation P iotaO M.space M.universal
  let V := (Over.map M.space.hom).obj Z
  have : LocallyOfFiniteType Z.hom := hft
  have : LocallyOfFiniteType V.hom := inferInstanceAs (LocallyOfFiniteType (Z.hom ≫ M.space.hom))
  exact ⟨V, hn, inferInstance, PELModuli.IntegralModel.Relative.FamilyClassification.relativePELUniversal P iotaO M.space M.universal Z u,
    Relative.PELParameterClassification.relativePELParameter_classifies P iotaO M hM hN u hclass⟩

def nativePELPullbackIso_of_integralComparison
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {V T : Over (Spec (.of K))}
    (U : PELModuli.IntegralModel.PEL.Has.IntegralPELObject P K (iota.comp (algebraMap (NumberField.RingOfIntegers E) E)) N V)
    (B : PEL.Objects.PELObject P iota N T) (f : T ⟶ V)
    (e : PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso (U.data.pullback f.left) (PELModuli.IntegralModel.PEL.BaseChange.integralPELOfCharacteristicZero B).data) :
    Models.PELPullbackIso U.toCharacteristicZero B f :=
  Models.PELPullbackIso.ofPELIso { polarized := e.symm.polarized, action := e.symm.action }

def integralComparison_of_nativePELPullbackIso
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {V T : Over (Spec (.of K))}
    (U : PELModuli.IntegralModel.PEL.Has.IntegralPELObject P K (iota.comp (algebraMap (NumberField.RingOfIntegers E) E)) N V)
    (B : PEL.Objects.PELObject P iota N T) (f : T ⟶ V) (e : Models.PELPullbackIso U.toCharacteristicZero B f) :
    PELModuli.IntegralModel.PEL.Iso.PolarizedActionIso (U.data.pullback f.left) (PELModuli.IntegralModel.PEL.BaseChange.integralPELOfCharacteristicZero B).data where
  polarized := e.toPELIso.symm.polarized
  action := e.toPELIso.symm.action

theorem exists_fine_pel_model_of_fine_pure
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s N : ℕ} (P : Datum.RankThreePELDatum E s) (iota : E →+* K)
    (M : Pure.Fine.PurePolarizedModel (3 * s) P.polarizationType N (Spec (.of K)))
    [IsNoetherian M.space.left] [LocallyOfFiniteType M.space.hom] (hM : M.IsFine) (hN : 3 ≤ N) :
    ∃ F : Models.FinePELModel P iota N, F.IsFine ∧ IsNoetherian F.space.left ∧ LocallyOfFiniteType F.space.hom := by
  have : Countable K := NumberFieldCountability.numberField_countable K
  obtain ⟨V, hn, hft, U, hc⟩ := exists_field_prescribed_pel_classifier P
    (iota.comp (algebraMap (NumberField.RingOfIntegers E) E)) M hM hN
  refine ⟨⟨V, U.toCharacteristicZero⟩, ?_, hn, hft⟩
  intro T B
  obtain ⟨f, ⟨e⟩, hf⟩ := hc T (PELModuli.IntegralModel.PEL.BaseChange.integralPELOfCharacteristicZero B)
  refine ⟨f, ⟨nativePELPullbackIso_of_integralComparison U B f e⟩, ?_⟩
  rintro k ⟨a⟩
  exact hf k ⟨integralComparison_of_nativePELPullbackIso U B k a⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FieldPrescribedPELFine
