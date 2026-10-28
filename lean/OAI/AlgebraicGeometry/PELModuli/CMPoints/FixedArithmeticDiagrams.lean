import OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedCoefficientDiagrams
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ModelLifts

/-! # Fixed Arithmetic Diagrams -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedArithmeticDiagrams

noncomputable section

/-! Generic diagrams between fixed arithmetic models extend after
one enlargement of the original rational denominator. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
  (B : IntegralModel.Base.ArithmeticBaseExtension K κ)

def arithmeticModelProjection (X : Over B.base)
    {G : Over (Spec (.of B.extension.carrier))} (p : G.left ⟶ X.left)
    (hp : p ≫ X.hom = G.hom ≫ B.generic)
    (D : ℕ) (hD : D ≠ 0) (hdiv : B.denominator ∣ D) :
    G.left ⟶ ((Over.pullback (ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv)).obj X).left :=
  ModelLifts.modelLift X p (ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv) (B.withDenominator D hD).generic
    (hp.trans (congrArg (fun z => G.hom ≫ z) (ArithmeticBaseMaps.arithmeticEnlargement_generic B D hD hdiv).symm))

@[reassoc]
theorem arithmeticModelProjection_fst (X : Over B.base)
    {G : Over (Spec (.of B.extension.carrier))} (p : G.left ⟶ X.left)
    (hp : p ≫ X.hom = G.hom ≫ B.generic)
    (D : ℕ) (hD : D ≠ 0) (hdiv : B.denominator ∣ D) :
    arithmeticModelProjection B X p hp D hD hdiv ≫
      pullback.fst X.hom (ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv) = p :=
  ModelLifts.modelLift_fst _ _ _ _ _

@[reassoc]
theorem arithmeticModelProjection_snd (X : Over B.base)
    {G : Over (Spec (.of B.extension.carrier))} (p : G.left ⟶ X.left)
    (hp : p ≫ X.hom = G.hom ≫ B.generic)
    (D : ℕ) (hD : D ≠ 0) (hdiv : B.denominator ∣ D) :
    arithmeticModelProjection B X p hp D hD hdiv ≫
      pullback.snd X.hom (ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv) =
        G.hom ≫ (B.withDenominator D hD).generic :=
  ModelLifts.modelLift_snd _ _ _ _ _

theorem finite_morphisms_between_fixed_arithmetic_models_spread
    {I J : Type*} [Finite J] (src dst : J → I)
    (X : I → Over B.base) (G : I → Over (Spec (.of B.extension.carrier)))
    (hX : ∀ i, ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (X i).hom)
    (p : ∀ i, (G i).left ⟶ (X i).left)
    (hp : ∀ i, IsPullback (p i) (G i).hom (X i).hom B.generic)
    (a : ∀ j, G (src j) ⟶ G (dst j)) :
    ∃ (D : ℕ) (hD : D ≠ 0) (hdiv : B.denominator ∣ D),
      ∃ b : ∀ j, (Over.pullback (ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv)).obj (X (src j)) ⟶
        (Over.pullback (ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv)).obj (X (dst j)),
        ∀ j, arithmeticModelProjection B (X (src j)) (p (src j)) (hp (src j)).w D hD hdiv ≫
          (b j).left = (a j).left ≫
            arithmeticModelProjection B (X (dst j)) (p (dst j)) (hp (dst j)).w D hD hdiv := by
  let : Algebra B.R B.extension.carrier := B.toField.toAlgebra
  obtain ⟨t, b, hb⟩ := FixedCoefficientDiagrams.finite_morphisms_between_fixed_coefficient_models_descend
    src dst X G hX p hp a
  obtain ⟨D, hD, hdiv, φ, hφ, hφbase⟩ := ArithmeticCoefficientEnlargement.arithmetic_coefficients_localize B t
  let B' := B.withDenominator D hD
  let u : B'.base ⟶ ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientBase B.R B.extension.carrier t :=
    Spec.map (CommRingCat.ofHom φ)
  have hu : u ≫ EmptyCoefficientBase.coefficientStructureMap t = ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv := by
    change Spec.map (CommRingCat.ofHom φ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B.R (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.coefficientRing B.R B.extension.carrier t))) = _
    rw [← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hφbase
  have hv : B'.generic ≫ u = ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap B.R B.extension.carrier t := by
    change Spec.map (CommRingCat.ofHom B'.toField) ≫ Spec.map (CommRingCat.ofHom φ) = _
    rw [← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hφ
  let Xt i := (Over.pullback (EmptyCoefficientBase.coefficientStructureMap t)).obj (X i)
  let pt i := FixedCoefficientModels.fixedCoefficientProjection (X i) (p i) (hp i) t
  have hpt i : pt i ≫ (Xt i).hom = (G i).hom ≫ B'.generic ≫ u :=
    (FixedCoefficientModels.fixedCoefficientProjection_snd (X i) (p i) (hp i) t).trans
      (congrArg (fun z => (G i).hom ≫ z) hv.symm)
  let pd i := ModelLifts.modelLift (Xt i) (pt i) u B'.generic (hpt i)
  let e i := IntegralModel.Group.BaseChangeComparisons.GroupBaseChange.iteratedIso (X i) (EmptyCoefficientBase.coefficientStructureMap t)
    u (ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv) hu
  have he i : pd i ≫ (e i).hom.left =
      arithmeticModelProjection B (X i) (p i) (hp i).w D hD hdiv := by
    exact ModelLifts.modelLift_iterated (X i) (p i) (EmptyCoefficientBase.coefficientStructureMap t)
      (ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations.genericBaseMap B.R B.extension.carrier t)
      ((hp i).w.trans (congrArg (fun z => (G i).hom ≫ z) (EmptyCoefficientBase.genericBaseMap_structure t).symm))
      u (ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv) hu B'.generic hv _
  have hei i : arithmeticModelProjection B (X i) (p i) (hp i).w D hD hdiv ≫
      (e i).inv.left = pd i :=
    (((Over.forget _).mapIso (e i)).eq_comp_inv.mpr (he i)).symm
  refine ⟨D, hD, hdiv, fun j => (e (src j)).inv ≫ (Over.pullback u).map (b j) ≫
    (e (dst j)).hom, ?_⟩
  intro j
  have hm : pd (src j) ≫ ((Over.pullback u).map (b j)).left = (a j).left ≫ pd (dst j) :=
    ModelLifts.modelLift_map (Xt (src j)) (pt (src j)) u B'.generic (hpt (src j))
      (pt (dst j)) (hpt (dst j)) (a j) (b j) (hb j)
  change _ ≫ ((e (src j)).inv.left ≫
    (((Over.pullback u).map (b j)).left ≫ (e (dst j)).hom.left)) = _
  rw [← Category.assoc, hei, ← Category.assoc, hm, Category.assoc, he]

theorem morphism_between_fixed_arithmetic_models_spreads
    (X Y : Over B.base)
    (hX : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism X.hom) (hY : ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism Y.hom)
    {G H : Over (Spec (.of B.extension.carrier))}
    (p : G.left ⟶ X.left) (q : H.left ⟶ Y.left)
    (hp : IsPullback p G.hom X.hom B.generic)
    (hq : IsPullback q H.hom Y.hom B.generic) (a : G ⟶ H) :
    ∃ (D : ℕ) (hD : D ≠ 0) (hdiv : B.denominator ∣ D),
      ∃ b : (Over.pullback (ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv)).obj X ⟶
        (Over.pullback (ArithmeticBaseMaps.arithmeticEnlargement B D hD hdiv)).obj Y,
        arithmeticModelProjection B X p hp.w D hD hdiv ≫ b.left =
          a.left ≫ arithmeticModelProjection B Y q hq.w D hD hdiv := by
  let Z : Bool → Over B.base | false => X | true => Y
  let U : Bool → Over (Spec (.of B.extension.carrier)) | false => G | true => H
  let π : ∀ i, (U i).left ⟶ (Z i).left | false => p | true => q
  have hπ : ∀ i, IsPullback (π i) (U i).hom (Z i).hom B.generic
    | false => hp | true => hq
  have hZ : ∀ i, ArithmeticGeometry.Models.Scheme.Constructions.Foundations.FinitePresentationMorphism (Z i).hom | false => hX | true => hY
  obtain ⟨D, hD, hdiv, b, hb⟩ := finite_morphisms_between_fixed_arithmetic_models_spread B
    (fun _ : Unit => false) (fun _ => true) Z U hZ π hπ (fun _ => a)
  exact ⟨D, hD, hdiv, b (), hb ()⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.FixedArithmeticDiagrams
