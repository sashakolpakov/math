import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ConstantDeRhamNaturality
import OAI.AlgebraicGeometry.ComplexMultiplication.CMComparisonTo

/-! # Coefficient Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CoefficientNaturality

noncomputable section

/-! # Actual inverse-image transport is natural in original coefficients

This uses the original constant complex functor and the canonical coefficient
identity, including the unchanged rational-to-complex inclusion.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint

variable {X Y : Over (Spec (.of ℂ))}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Original nonnegative constant transport commutes with every actual coefficient map. -/
theorem originalConstantComplexInverseImageIsoNat_naturality (f : X ⟶ Y)
    {A B : AddCommGrpCat} (g : A ⟶ B) :
    ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((CochainComplex.single₀ (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y)).map
          ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))).map g)) ≫
      (ConstantNaturality.originalConstantComplexInverseImageIsoNat f B).hom =
    (ConstantNaturality.originalConstantComplexInverseImageIsoNat f A).hom ≫
      (CochainComplex.single₀ (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)).map
        ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).map g) := by
  refine HomologicalComplex.hom_ext _ _ (fun i ↦ ?_)
  cases i with
  | zero =>
    change (AnalyticInverseImage.originalAnalyticSheafInverseImage f).map
        ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))).map g) ≫
      (ConstantNaturality.originalConstantComplexInverseImageIsoNat f B).hom.f 0 =
      (ConstantNaturality.originalConstantComplexInverseImageIsoNat f A).hom.f 0 ≫
        (AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).map g
    rw [ConstantNaturality.originalConstantComplexInverseImageIsoNat_hom_zero,
      ConstantNaturality.originalConstantComplexInverseImageIsoNat_hom_zero]
    exact (AnalyticInverseImage.originalAnalyticConstantInverseImageIso f).hom.naturality g
  | succ n =>
    exact ((AnalyticInverseImage.originalAnalyticSheafInverseImage f).map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 _ (n + 1)
        (Nat.succ_ne_zero n))).eq_of_src _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Original integer constant transport commutes with every actual coefficient map. -/
theorem originalCoefficientComplexInverseImageIso_naturality (f : X ⟶ Y)
    {A B : AddCommGrpCat} (g : A ⟶ B) :
    (AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.map ((CMComparisonTo.coefficientComplexFunctor Y).map g) ≫
        (ConstantDeRhamNaturality.originalCoefficientComplexInverseImageIso f B).hom =
      (ConstantDeRhamNaturality.originalCoefficientComplexInverseImageIso f A).hom ≫
        (CMComparisonTo.coefficientComplexFunctor X).map g := by
  unfold ConstantDeRhamNaturality.originalCoefficientComplexInverseImageIso
  change (((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap
        ((CochainComplex.single₀ (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y)).map
          ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))).map g))
        ComplexShape.embeddingUpNat) ≫
      (OAI.Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (AnalyticInverseImage.originalAnalyticSheafInverseImage f)
        ((CochainComplex.single₀ (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y)).obj
          ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))).obj B))
        ComplexShape.embeddingUpNat).hom) ≫
      HomologicalComplex.extendMap (ConstantNaturality.originalConstantComplexInverseImageIsoNat f B).hom
        ComplexShape.embeddingUpNat = _
  rw [OAI.Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso_naturality, Category.assoc,
    ← HomologicalComplex.extendMap_comp, originalConstantComplexInverseImageIsoNat_naturality]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    HomologicalComplex.extendMap_comp]
  rfl

variable (R : Type) [Field R] [Algebra R ℂ]
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The unchanged original field-to-holomorphic complex inclusion commutes with scheme pullback. -/
theorem originalDeRhamInverseImagePullback_fieldComparison (f : X ⟶ Y) :
    (AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.map
        (ComplexPoint.Basic.ComplexSchemePoint.fieldToHolomorphicDeRhamComplexInt R Y) ≫ InverseImageMap.originalDeRhamInverseImagePullback f =
      (ConstantDeRhamNaturality.originalCoefficientComplexInverseImageIso f (AddCommGrpCat.of R)).hom ≫
        ComplexPoint.Basic.ComplexSchemePoint.fieldToHolomorphicDeRhamComplexInt R X := by
  have hc : (AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.map
        (ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt R Y) ≫
      (ConstantDeRhamNaturality.originalComplexComplexInverseImageIso f).hom =
    (ConstantDeRhamNaturality.originalCoefficientComplexInverseImageIso f (AddCommGrpCat.of R)).hom ≫
      ComplexPoint.Basic.ComplexSchemePoint.fieldToComplexConstantSheafComplexInt R X :=
    originalCoefficientComplexInverseImageIso_naturality f
      (AddCommGrpCat.ofHom (algebraMap R ℂ).toAddMonoidHom)
  unfold ComplexPoint.Basic.ComplexSchemePoint.fieldToHolomorphicDeRhamComplexInt
  rw [Functor.map_comp, Category.assoc, ConstantDeRhamNaturality.originalDeRhamInverseImagePullback_constants,
    ← Category.assoc, hc, Category.assoc]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CoefficientNaturality
