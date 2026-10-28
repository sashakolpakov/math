import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ConstantNaturality
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredPullback

/-! # Constant De Rham Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ConstantDeRhamNaturality

noncomputable section

/-! # Original constant-to-de Rham comparison under genuine scheme pullback

All coefficient and de Rham complexes are the original complexes. Their actual
inverse-image maps commute with the original comparison in every integer degree.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace

variable {X Y : Over (Spec (.of ℂ))}

/-- Genuine inverse image of an original constant coefficient complex, extended by zero. -/
def originalCoefficientComplexInverseImageIso (f : X ⟶ Y) (A : AddCommGrpCat) :
    (AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj
        (((CochainComplex.single₀ (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y)).obj
          ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))).obj A)).extend
            ComplexShape.embeddingUpNat) ≅
      ((CochainComplex.single₀ (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)).obj
        ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).obj A)).extend
          ComplexShape.embeddingUpNat :=
  Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (AnalyticInverseImage.originalAnalyticSheafInverseImage f)
    ((CochainComplex.single₀ (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf Y)).obj
      ((AlgebraicTopology.Sheaf.Constant.TopCat.constantFunctor (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint Y))).obj A))
        ComplexShape.embeddingUpNat ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (ComplexPoint.Basic.ComplexSchemePoint.AnalyticAdditiveSheaf X)).mapIso
      (ConstantNaturality.originalConstantComplexInverseImageIsoNat f A)

/-- The actual original constant complex transports by the actual coefficient identity. -/
def originalComplexComplexInverseImageIso (f : X ⟶ Y) :
    (AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.obj
      (ComplexPoint.Basic.ComplexSchemePoint.constantComplexSheafComplexInt Y) ≅ ComplexPoint.Basic.ComplexSchemePoint.constantComplexSheafComplexInt X :=
  originalCoefficientComplexInverseImageIso f (AddCommGrpCat.of ℂ)

variable [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Genuine scheme pullback commutes with the original integer-indexed constant inclusion. -/
theorem originalDeRhamInverseImagePullback_constants (f : X ⟶ Y) :
    (AnalyticInverseImage.originalAnalyticInverseImageLocalizer f).functor.map
        (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt Y) ≫ InverseImageMap.originalDeRhamInverseImagePullback f =
      (originalComplexComplexInverseImageIso f).hom ≫
        ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X := by
  unfold InverseImageMap.originalDeRhamInverseImagePullback originalComplexComplexInverseImageIso
    originalCoefficientComplexInverseImageIso ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt
  change (((AnalyticInverseImage.originalAnalyticSheafInverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplex Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left))
        ComplexShape.embeddingUpNat) ≫
      (Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso (AnalyticInverseImage.originalAnalyticSheafInverseImage f)
        (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamComplex Y (Topology.Dimension.Basic.TopologicalSpace.dim Y.left)) ComplexShape.embeddingUpNat).hom) ≫
        HomologicalComplex.extendMap (InverseImageMap.originalDeRhamInverseImagePullbackNat f)
          ComplexShape.embeddingUpNat = _
  rw [Algebra.Homology.MapExtend.HomologicalComplex.mapExtendCanonicalIso_naturality, Category.assoc,
    ← HomologicalComplex.extendMap_comp,
    ConstantNaturality.originalDeRhamInverseImagePullbackNat_constants]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    HomologicalComplex.extendMap_comp]
  rfl

/-- Actual original complex-constant hypercohomology pullback. -/
def originalComplexConstantHypercohomologyPullback (f : X ⟶ Y) (n : ℤ) :
    ComplexPoint.Basic.ComplexSchemePoint.ComplexConstantCohomology Y n → ComplexPoint.Basic.ComplexSchemePoint.ComplexConstantCohomology X n := fun α =>
  ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (originalComplexComplexInverseImageIso f).hom n
    (HypercohomologyPullback.originalHypercohomologyPullback f (ComplexPoint.Basic.ComplexSchemePoint.constantComplexSheafComplexInt Y) n α)

/-- The original constant-to-de Rham map is natural on the actual original hypercohomology. -/
theorem originalDeRhamHypercohomologyPullback_constantComparison (f : X ⟶ Y)
    (n : ℤ) (α : ComplexPoint.Basic.ComplexSchemePoint.ComplexConstantCohomology Y n) :
    FilteredPullback.originalDeRhamHypercohomologyPullback f n (ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamEquiv Y n α) =
      ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamEquiv X n
        (originalComplexConstantHypercohomologyPullback f n α) := by
  change FilteredPullback.originalDeRhamHypercohomologyPullback f n
      (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap Y (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt Y) n α) =
    ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.constantsToHolomorphicDeRhamComplexInt X) n
      (originalComplexConstantHypercohomologyPullback f n α)
  unfold FilteredPullback.originalDeRhamHypercohomologyPullback
    originalComplexConstantHypercohomologyPullback
  rw [HypercohomologyPullback.originalHypercohomologyPullback_naturality,
    ← ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply, ← ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap_comp_apply,
    originalDeRhamInverseImagePullback_constants]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.ConstantDeRhamNaturality
