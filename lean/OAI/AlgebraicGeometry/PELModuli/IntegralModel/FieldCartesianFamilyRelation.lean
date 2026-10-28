import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FamilyRelation
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NumberFieldCoefficient
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OverIsoNaturality
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FunctorComparison

/-! # Field Cartesian Family Relation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldCartesianFamilyRelation

noncomputable section

/-! A generic family and its fixed arithmetic overlap relation extend
over one larger denominator, preserving the actual generic family diagram. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Cartesian.FamilyRelation.Coefficients

theorem numberField_cartesian_family_relation_model
    {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ) [Algebra B.R B.extension.carrier]
    (hAlg : algebraMap B.R B.extension.carrier = B.toField)
    {Z W T X : Over B.base}
    (hZ : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Z.hom)
    (hW : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism W.hom) (hT : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism T.hom)
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (v w : Z ⟶ W) (a : W ⟶ T) (u : T ⟶ X)
    (Y : Over (Spec (.of B.extension.carrier))) (hY : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom)
    (q : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R B.extension.carrier)))).obj W ⟶ Y)
    (b : Y ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R B.extension.carrier)))).obj X)
    (hc : IsPullback ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R B.extension.carrier)))).map a) q
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R B.extension.carrier)))).map u) b)
    (he : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R B.extension.carrier)))).map v ≫ q =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R B.extension.carrier)))).map w ≫ q)
    (N₀ : ℕ) (hN₀ : N₀ ≠ 0) :
    ∃ (N : ℕ) (hN : N ≠ 0), N₀ ∣ N ∧
      let D := B.withDenominator N hN
      ∃ φ : B.R →+* D.R, D.toField.comp φ = B.toField ∧
        let F := Over.pullback (Spec.map (CommRingCat.ofHom φ))
        ∃ (Y₀ : Over D.base) (q₀ : F.obj W ⟶ Y₀) (b₀ : Y₀ ⟶ F.obj X),
          ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y₀.hom ∧ IsPullback (F.map a) q₀ (F.map u) b₀ ∧
          F.map v ≫ q₀ = F.map w ≫ q₀ ∧
          ∃ ec : F ⋙ Over.pullback D.generic ≅
            Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R B.extension.carrier))),
          ∃ ey : (Over.pullback D.generic).obj Y₀ ≅ Y,
            (Over.pullback D.generic).map q₀ ≫ ey.hom = (ec.app W).hom ≫ q ∧
            (Over.pullback D.generic).map b₀ ≫ (ec.app X).hom = ey.hom ≫ b := by
  obtain ⟨M, b₀, q₀, hb₀, hq₀, hcart, hcoeq⟩ :=
    Cartesian.FamilyRelation.Coefficients.generic_cartesian_family_relation_has_coefficient_model hZ hW hT hX v w a u Y hY q b hc he
  obtain ⟨N, hN, hdiv, ψ, hψ, hbase⟩ := B.generic_coefficients_extend_over_integers hAlg M.coefficients N₀ hN₀
  let D := B.withDenominator N hN
  let φ := ψ.comp (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R B.extension.carrier M.coefficients))
  let f := Fixed.CoefficientModels.Coefficients.parameterBaseMap B.R B.extension.carrier M.coefficients
  let k := Spec.map (CommRingCat.ofHom ψ)
  let c := Spec.map (CommRingCat.ofHom φ)
  let g := ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap B.R B.extension.carrier M.coefficients
  have hkc : k ≫ f = c :=
    (Spec.map_comp (CommRingCat.ofHom (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R B.extension.carrier M.coefficients)))
      (CommRingCat.ofHom ψ)).symm
  have hgk : D.generic ≫ k = g := by
    change Spec.map (CommRingCat.ofHom D.toField) ≫ Spec.map (CommRingCat.ofHom ψ) = _
    rw [← Spec.map_comp]
    exact congrArg (fun r => Spec.map (CommRingCat.ofHom r)) hψ
  let P := Over.pullback f
  let H := Over.pullback k
  let F := Over.pullback c
  let e := Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso f k c hkc
  let Y₀ := H.obj M.model
  let q₁ : F.obj W ⟶ Y₀ := (e.app W).inv ≫ H.map q₀
  let b₁ : Y₀ ⟶ F.obj X := H.map b₀ ≫ (e.app X).hom
  have ha : H.map (P.map a) ≫ (e.app T).hom = (e.app W).hom ≫ F.map a := e.hom.naturality a
  have hu : H.map (P.map u) ≫ (e.app X).hom = (e.app T).hom ≫ F.map u := e.hom.naturality u
  have hs : IsPullback (F.map a) q₁ (F.map u) b₁ := by
    exact (hcart.map H).of_iso (e.app W) (e.app T) (Iso.refl Y₀) (e.app X) ha
      (by
        change H.map q₀ ≫ 𝟙 _ = (e.app W).hom ≫ ((e.app W).inv ≫ H.map q₀)
        rw [Category.comp_id, Iso.hom_inv_id_assoc]) hu
      (by
        change H.map b₀ ≫ (e.app X).hom = 𝟙 _ ≫ (H.map b₀ ≫ (e.app X).hom)
        exact (Category.id_comp _).symm)
  have hn (r : Z ⟶ W) : F.map r ≫ (e.app W).inv =
      (e.app Z).inv ≫ H.map (P.map r) := e.inv.naturality r
  have hcoeq₁ : F.map v ≫ q₁ = F.map w ≫ q₁ := by
    change F.map v ≫ ((e.app W).inv ≫ H.map q₀) =
      F.map w ≫ ((e.app W).inv ≫ H.map q₀)
    rw [← Category.assoc, hn v, Category.assoc, ← H.map_comp,
      ← Category.assoc, hn w, Category.assoc, ← H.map_comp, hcoeq]
  let eg := Group.BaseChangeComparisons.GroupBaseChange.iteratedNatIso k D.generic g hgk
  let J := Over.pullback D.generic
  let L := Over.pullback g
  let G := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap B.R B.extension.carrier)))
  let ew : L.obj (P.obj W) ≅ G.obj W := (Fixed.CoefficientModels.Coefficients.fixedSourceComparison B.R B.extension.carrier M.coefficients).app W
  let ex : L.obj (P.obj X) ≅ G.obj X := (Fixed.CoefficientModels.Coefficients.fixedSourceComparison B.R B.extension.carrier M.coefficients).app X
  let em : L.obj M.model ≅ Y := M.genericIso
  have hqg : L.map q₀ ≫ em.hom = ew.hom ≫ q :=
    OverIsoNaturality.over_model_iso_naturality g ew em q q₀ hq₀
  have hbg : L.map b₀ ≫ ex.hom = em.hom ≫ b :=
    OverIsoNaturality.over_model_iso_naturality g em ex b b₀ hb₀
  obtain ⟨ec, ey, hqcmp, hbcmp⟩ := Cartesian.FunctorComparison.cartesian_functor_comparison P H F J L G e eg
    (Fixed.CoefficientModels.Coefficients.fixedSourceComparison B.R B.extension.carrier M.coefficients) em q₀ b₀ q b hqg hbg
  exact ⟨N, hN, hdiv, φ, hbase, Y₀, q₁, b₁,
    Coefficient.Finiteness.Coefficients.baseChange_finitePresentation k M.model M.finitePresentation, hs, hcoeq₁, ec, ey,
    hqcmp, hbcmp⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldCartesianFamilyRelation
