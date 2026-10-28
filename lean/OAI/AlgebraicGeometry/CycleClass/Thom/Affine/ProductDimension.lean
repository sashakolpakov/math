import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DimensionBridge
import OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.TranscendenceDimension
import OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs

/-! # Product Dimension -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductDimension.Constructions

noncomputable section

/-! Dimensions of actual affine complex products, with scalar compatibility
proved for the canonical tensor-product coordinate isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.Affine.DimensionBridge.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.TranscendenceDimension.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductIs.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem affineOver_dimension (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] [IsIntegral X.left] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom = (Algebra.trdeg ℂ Γ(X.left, ⊤)).toNat := by
  let : IsIntegral (Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ Γ(X.left, ⊤)).left :=
    inferInstanceAs (IsIntegral (Spec (CommRingCat.of Γ(X.left, ⊤))))
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv.left X.hom
  rw [(Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv.w] at h
  exact h.symm.trans (DimensionBridge.Constructions.schemeTranscendenceDimension_spec_algebra ℂ Γ(X.left, ⊤))

@[reassoc]
theorem affineProductCoordinateIso_base (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsAffine X.left] [IsAffine Y.left] :
    (ProductIs.Constructions.affineProductCoordinateIso X Y).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (Γ(X.left, ⊤) ⊗[ℂ] Γ(Y.left, ⊤)))) =
    pullback.fst X.hom Y.hom ≫ X.hom := by
  let a := Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(X.left, ⊤)))
  let b := Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(Y.left, ⊤)))
  let t := pullback.map X.hom Y.hom a b
    (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).hom.left (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso Y).hom.left (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
    (by rw [Category.comp_id]; exact (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).hom.w.symm)
    (by rw [Category.comp_id]; exact (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso Y).hom.w.symm)
  have ht : t ≫ pullback.fst a b = pullback.fst X.hom Y.hom ≫ (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).hom.left :=
    pullback.lift_fst _ _ _
  change (t ≫ (pullbackSpecIso ℂ Γ(X.left, ⊤) Γ(Y.left, ⊤)).hom) ≫ _ = _
  rw [Category.assoc, pullbackSpecIso_hom_base]
  change t ≫ (pullback.fst a b ≫ a) = _
  rw [← Category.assoc, ht, Category.assoc]
  exact congrArg (fun f => pullback.fst X.hom Y.hom ≫ f) (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).hom.w

theorem affineProduct_dimension (X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsAffine X.left] [IsAffine Y.left] [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    letI := ProductIs.Constructions.affineProduct_isIntegral X Y
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (pullback.fst X.hom Y.hom ≫ X.hom) =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom + Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom := by
  let := ProductIs.Constructions.affineProduct_isIntegral X Y
  let : Algebra.FiniteType ℂ Γ(X.left, ⊤) := ComplexPoints.Analytic.FiniteTypeSchemeTopology.affineOverGamma_finiteType X
  let : Algebra.FiniteType ℂ Γ(Y.left, ⊤) := ComplexPoints.Analytic.FiniteTypeSchemeTopology.affineOverGamma_finiteType Y
  let : IsDomain (Γ(X.left, ⊤) ⊗[ℂ] Γ(Y.left, ⊤)) :=
    Tensor.ProductDomain.Constructions.tensorProduct_isDomain
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion (ProductIs.Constructions.affineProductCoordinateIso X Y).hom
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Γ(X.left, ⊤) ⊗[ℂ] Γ(Y.left, ⊤)))))
  rw [affineProductCoordinateIso_base] at h
  rw [h, DimensionBridge.Constructions.schemeTranscendenceDimension_spec_algebra, Tensor.TranscendenceDimension.Constructions.tensorProduct_trdeg,
    Cardinal.toNat_add (trdeg_lt_aleph0_of_finiteType (R := ℂ) (S := Γ(X.left, ⊤)))
      (trdeg_lt_aleph0_of_finiteType (R := ℂ) (S := Γ(Y.left, ⊤))),
    affineOver_dimension X, affineOver_dimension Y]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Affine.ProductDimension.Constructions
