import OAI.AlgebraicGeometry.PELModuli.CMPoints.GenericProjectionMaps
import OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedArithmeticIsomorphisms

/-! # Fixed Abelian Isomorphisms -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedAbelianIsomorphisms

noncomputable section

/-! Extend a specified generic abelian isomorphism while preserving
its group structure and its exact generic comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem abelian_iso_between_fixed_arithmetic_models_spreads
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : IntegralModel.Base.ArithmeticBaseExtension K κ) {g h : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g B.base) (C : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h B.base)
    (e : (A.pullback B.generic).scheme ≅ (C.pullback B.generic).scheme) [IsMonHom e.hom] :
    ∃ (D : ℕ) (hD : D ≠ 0) (hdiv : B.denominator ∣ D),
      ∃ eD : (A.pullback (ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv)).scheme ≅
        (C.pullback (ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv)).scheme,
        IsMonHom eD.hom ∧
        (Over.pullback (B.withDenominator D hD).generic).map eD.hom ≫
          (GenericProjectionMaps.arithmeticGenericComparison B C.scheme D hD hdiv).hom =
            (GenericProjectionMaps.arithmeticGenericComparison B A.scheme D hD hdiv).hom ≫ e.hom := by
  obtain ⟨D, hD, hdiv, eD, heD⟩ := FixedArithmeticIsomorphisms.iso_between_fixed_arithmetic_models_spreads B A.scheme C.scheme
    ⟨inferInstance, inferInstance, inferInstance⟩ ⟨inferInstance, inferInstance, inferInstance⟩
    (pullback.fst A.scheme.hom B.generic) (pullback.fst C.scheme.hom B.generic)
    (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _) e
  let B' := B.withDenominator D hD
  let u := ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv
  let eA := GenericProjectionMaps.arithmeticGenericComparison B A.scheme D hD hdiv
  let eC := GenericProjectionMaps.arithmeticGenericComparison B C.scheme D hD hdiv
  have hc : (Over.pullback B'.generic).map eD.hom ≫ eC.hom = eA.hom ≫ e.hom := by
    apply GenericProjectionMaps.generic_map_of_projection_comparison B'.generic eA eC eD.hom e.hom
    rw [GenericProjectionMaps.arithmeticGenericComparison_projection, GenericProjectionMaps.arithmeticGenericComparison_projection]
    exact heD
  let : IsMonHom eA.hom := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_isMonHom _ _ _ _ _
  let : IsMonHom eC.hom := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso_isMonHom _ _ _ _ _
  have hf : (Over.pullback B'.generic).map eD.hom = (eA.hom ≫ e.hom) ≫ eC.inv :=
    eC.eq_comp_inv.mpr hc
  let : IsMonHom ((Over.pullback B'.generic).map eD.hom) := by
    rw [hf]
    exact @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _
      (@CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ eA.hom e.hom
        (inferInstanceAs (IsMonHom eA.hom)) (inferInstanceAs (IsMonHom e.hom)))
      (inferInstanceAs (IsMonHom eC.inv))
  let : IsDomain B'.R := Function.Injective.isDomain B'.toField B'.toField_injective
  let : IsReduced B'.base := inferInstanceAs (IsReduced (Spec (.of B'.R)))
  let : IsLocallyNoetherian B'.base := inferInstanceAs (IsLocallyNoetherian (Spec (.of B'.R)))
  let : IsDominant B'.generic := B'.generic_dominant
  let : Smooth ((Over.pullback u).obj A.scheme).hom := inferInstanceAs (Smooth (pullback.snd A.scheme.hom u))
  let : IsSeparated ((Over.pullback u).obj C.scheme).hom :=
    inferInstanceAs (IsSeparated (pullback.snd C.scheme.hom u))
  exact ⟨D, hD, hdiv, eD, GroupMapReflection.isMonHom_of_dominant_baseChange B'.generic eD.hom, hc⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedAbelianIsomorphisms
