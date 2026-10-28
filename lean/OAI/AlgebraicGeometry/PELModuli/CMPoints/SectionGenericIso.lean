import OAI.AlgebraicGeometry.PELModuli.CMPoints.SpreadReferenceComparison
import OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedAbelianIsomorphisms

/-! # Section Generic Iso -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints

noncomputable section

section

/-! Compare the spread original object with the PEL family pulled back
along the extended CM section, retaining the actual generic group map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : Models.RankThreePELModel E K} {hM : M.HasPrescribedBallPeriods}
  {a : M.Family} {t : Fin (M.componentCount a)} (C : M.CMSpreadData hM a t)
  (D : ℕ) (hD : D ≠ 0) (hdiv : C.base.denominator ∣ D)
  (z : (C.base.withDenominator D hD).base ⟶ ((M.components a).S t).left)
  (hz : (C.base.withDenominator D hD).generic ≫ z = C.fieldPoint)

def Models.RankThreePELModel.CMSpreadData.sectionGenericIso :
    (((C.original.pullback (ArithmeticBaseMaps.arithmeticEnlargement C.base D hD hdiv)).pullback
      (C.base.withDenominator D hD).generic)).scheme ≅
        (((M.componentPolarized a t).abelian.pullback z).pullback
          (C.base.withDenominator D hD).generic).scheme :=
  GenericProjectionMaps.arithmeticGenericComparison C.base C.original.scheme D hD hdiv ≪≫
    C.originalGenericComparison ≪≫
      (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso (M.componentPolarized a t).abelian.scheme z
        (C.base.withDenominator D hD).generic C.fieldPoint hz).symm

theorem Models.RankThreePELModel.CMSpreadData.sectionGenericIso_group : IsMonHom (C.sectionGenericIso D hD hdiv z hz).hom := by
  let e := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso (M.componentPolarized a t).abelian.scheme z
    (C.base.withDenominator D hD).generic C.fieldPoint hz
  let : IsMonHom e.hom := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_isMonHom _ _ _ _ _
  exact @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _
    (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_isMonHom _ _ _ _ _)
    (@CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _
      C.originalGenericComparison_group (inferInstanceAs (IsMonHom e.inv)))

include hz in
theorem Models.RankThreePELModel.CMSpreadData.exists_extended_section_group_iso :
    ∃ (D' : ℕ) (hD' : D' ≠ 0) (hdiv' : D ∣ D'),
      ∃ e : (((C.original.pullback (ArithmeticBaseMaps.arithmeticEnlargement C.base D hD hdiv)).pullback
          (ArithmeticBaseMaps.arithmeticEnlargement (C.base.withDenominator D hD) D' hD' hdiv'))).scheme ≅
        (((M.componentPolarized a t).abelian.pullback z).pullback
          (ArithmeticBaseMaps.arithmeticEnlargement (C.base.withDenominator D hD) D' hD' hdiv')).scheme,
        IsMonHom e.hom := by
  let : IsMonHom (C.sectionGenericIso D hD hdiv z hz).hom := C.sectionGenericIso_group D hD hdiv z hz
  obtain ⟨D', hD', hdiv', e, he, _⟩ := FixedAbelianIsomorphisms.abelian_iso_between_fixed_arithmetic_models_spreads
    (C.base.withDenominator D hD) (C.original.pullback (ArithmeticBaseMaps.arithmeticEnlargement C.base D hD hdiv))
    ((M.componentPolarized a t).abelian.pullback z) (C.sectionGenericIso D hD hdiv z hz)
  exact ⟨D', hD', hdiv', e, he⟩

end

/-! The ordinary-factor diagram is realized on the fixed PEL family
along an actual integral section of the original component. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : Models.RankThreePELModel E K} {hM : M.HasPrescribedBallPeriods}
  {a : M.Family} {t : Fin (M.componentCount a)} (C : M.CMSpreadData hM a t)

structure Models.RankThreePELModel.CMSpreadData.IntegralComponentData where
  denominator : ℕ
  denominator_ne_zero : denominator ≠ 0
  denominator_divides : C.base.denominator ∣ denominator
  point : (C.base.withDenominator denominator denominator_ne_zero).base ⟶ ((M.components a).S t).left
  point_base : point ≫ ((M.components a).S t).hom =
    ArithmeticBaseMaps.arithmeticBaseMap M.arithmetic (C.base.withDenominator denominator denominator_ne_zero)
      C.originalFieldEmbedding (C.denominator_divides.trans denominator_divides)
  factor : Fin 3 → AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme (Fintype.card (NumberField.InfinitePlace E))
    (C.base.withDenominator denominator denominator_ne_zero).base
  action : ∀ i, AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) (factor i)
  splitting : TorsionFactorIso.AbelianScalarFactorization ((M.componentPolarized a t).abelian.pullback point) factor
  projective : ∀ i, Foundations.Scheme.SmoothProjective.ProjectivePresentation
    ((factor i).pullback (C.base.withDenominator denominator denominator_ne_zero).complexPoint).scheme.left
    ((factor i).pullback (C.base.withDenominator denominator denominator_ne_zero).complexPoint).scheme.hom

section

variable {C} (T : C.IntegralComponentData)

abbrev Models.RankThreePELModel.CMSpreadData.IntegralComponentData.base := C.base.withDenominator T.denominator T.denominator_ne_zero

def Models.RankThreePELModel.CMSpreadData.IntegralComponentData.polarized := (M.componentPolarized a t).pullback T.point

end

theorem Models.RankThreePELModel.CMSpreadData.exists_integral_component_data : Nonempty C.IntegralComponentData := by
  obtain ⟨D, hD, hdiv, z, hz, hzg⟩ := C.exists_integral_component_section
  obtain ⟨D', hD', hdiv', e, he⟩ := C.exists_extended_section_group_iso D hD hdiv z hzg
  let B₁ := C.base.withDenominator D hD
  let B₂ := C.base.withDenominator D' hD'
  let u₁ := ArithmeticBaseMaps.arithmeticEnlargement C.base D hD hdiv
  let u₂ := ArithmeticBaseMaps.arithmeticEnlargement B₁ D' hD' hdiv'
  let v : B₂.base ⟶ C.base.base := u₂ ≫ u₁
  let z' : B₂.base ⟶ ((M.components a).S t).left := u₂ ≫ z
  have hz' : z' ≫ ((M.components a).S t).hom =
      ArithmeticBaseMaps.arithmeticBaseMap M.arithmetic B₂ C.originalFieldEmbedding
        (C.denominator_divides.trans (hdiv.trans hdiv')) := by
    change (u₂ ≫ z) ≫ _ = _
    rw [Category.assoc, hz]
    exact ArithmeticBaseMaps.arithmeticBaseMap_enlarge M.arithmetic B₁ C.originalFieldEmbedding
      (C.denominator_divides.trans hdiv) D' hD' hdiv'
  let e₀ := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.compositeIso C.original.scheme u₁ u₂
  let e₁ := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso (M.componentPolarized a t).abelian.scheme z u₂ z' rfl
  let ec : (C.original.pullback v).scheme ≅ ((M.componentPolarized a t).abelian.pullback z').scheme :=
    e₀ ≪≫ e ≪≫ e₁
  have hec : IsMonHom ec.hom :=
    @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _
      (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.compositeIso_isMonHom _ _ _)
      (@CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ he
        (IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_isMonHom _ _ _ _ _))
  let factors (i : Fin 3) := (C.factor i).pullback v
  let split : TorsionFactorIso.AbelianScalarFactorization ((M.componentPolarized a t).abelian.pullback z') factors :=
    (C.splitting.pullback v).transport _ factors ec (fun i => Iso.refl (factors i).scheme) hec
      (fun i => inferInstanceAs (IsMonHom (𝟙 (factors i).scheme)))
  have hv : B₂.complexPoint ≫ v = C.base.complexPoint := by
    change B₂.complexPoint ≫ (u₂ ≫ u₁) = _
    rw [← Category.assoc]
    exact (congrArg (fun f => f ≫ u₁) (ArithmeticBaseMaps.arithmeticEnlargement_complex B₁ D' hD' hdiv')).trans
      (ArithmeticBaseMaps.arithmeticEnlargement_complex C.base D hD hdiv)
  have hP (i : Fin 3) : Foundations.Scheme.SmoothProjective.ProjectivePresentation ((factors i).pullback B₂.complexPoint).scheme.left
      ((factors i).pullback B₂.complexPoint).scheme.hom := by
    let ei := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso (C.factor i).scheme v B₂.complexPoint C.base.complexPoint hv
    have P := (C.factorProjective i).transportIso ((Over.forget Foundations.Scheme.ProjectiveSpace.complexBase).mapIso ei)
    change Foundations.Scheme.SmoothProjective.ProjectivePresentation _ (ei.hom.left ≫ ((C.factor i).pullback C.base.complexPoint).scheme.hom) at P
    have hw : ei.hom.left ≫ ((C.factor i).pullback C.base.complexPoint).scheme.hom =
        ((factors i).pullback B₂.complexPoint).scheme.hom := ei.hom.w
    exact hw ▸ P
  exact ⟨⟨D', hD', hdiv.trans hdiv', z', hz', factors, fun i => (C.action i).pullback v, split, hP⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints
