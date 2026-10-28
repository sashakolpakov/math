import OAI.RepresentationTheory.Theta.Geometric.ProductFiberMaps
import OAI.RepresentationTheory.Theta.Geometric.AbelianDifferenceBundle
import OAI.RepresentationTheory.Theta.Geometric.PoincareFormulaPullback
import OAI.RepresentationTheory.Theta.Geometric.FiberAmpleness
import OAI.RepresentationTheory.Theta.Geometric.LineBundleFieldTriviality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogenies

/-! # Quotient Difference Fibers -/

namespace OAI.RepresentationTheory.Theta.Geometric.QuotientDifferenceFibers

noncomputable section

/-! The descended difference formula has an ample, identity-normalized
line bundle on every geometric field fiber of the actual abelian model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {g h : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (p : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (Q : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (B.scheme ⊗ A.scheme).left)
    (recover : (Q.pullback (p.hom ⊗ₘ 𝟙 A.scheme).left).sheaf ≅ (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf)

def quotientDifference_formulaIso :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (Q.pullback (p.hom ⊗ₘ 𝟙 A.scheme).left).sheaf
        (L.pullback (fst A.scheme A.scheme).left).sheaf)
      (L.pullback (snd A.scheme A.scheme).left).sheaf ≅ (L.pullback μ[A.scheme].left).sheaf :=
  AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr recover (Iso.refl _)) (Iso.refl _) ≪≫
    (AbelianDifferenceBundle.abelianDifferenceBundle_formula A L).some

def quotientDifference_fiberFormulaIso (K : Type) [Field K] (z : Spec (.of K) ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) :
    let C := (A.pullback z).scheme
    let L' := L.pullback (Limits.pullback.fst A.scheme.hom z)
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
        (Q.pullback (ProductFiberMaps.productFiberMap A.scheme A.scheme z ≫ (p.hom ⊗ₘ 𝟙 A.scheme).left)).sheaf
        (L'.pullback (fst C C).left).sheaf)
      (L'.pullback (snd C C).left).sheaf ≅ (L'.pullback μ[C].left).sheaf :=
  AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr
      ((Scheme.Modules.pullbackComp (ProductFiberMaps.productFiberMap A.scheme A.scheme z)
        (p.hom ⊗ₘ 𝟙 A.scheme).left).app Q.sheaf).symm (Iso.refl _)) (Iso.refl _) ≪≫
    PoincareFormulaPullback.tensorFormulaPullbackIso (Limits.pullback.fst A.scheme.hom z) (ProductFiberMaps.productFiberMap A.scheme A.scheme z)
      (fst A.scheme A.scheme).left (snd A.scheme A.scheme).left μ[A.scheme].left
      (fst (A.pullback z).scheme (A.pullback z).scheme).left
      (snd (A.pullback z).scheme (A.pullback z).scheme).left μ[(A.pullback z).scheme].left
      (ProductFiberMaps.productFiberMap_fst A.scheme A.scheme z).symm
      (ProductFiberMaps.productFiberMap_snd A.scheme A.scheme z).symm (ProductFiberMaps.productFiberMap_mul A.scheme z)
      (Q.pullback (p.hom ⊗ₘ 𝟙 A.scheme).left) L (quotientDifference_formulaIso p L Q recover)

include recover in
theorem quotientDifference_positive_fiber (hL : L.IsAmple)
    (K : Type) [Field K] (z : Spec (.of K) ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) :
    let C := (A.pullback z).scheme
    ∃ L' : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle C.left, L'.IsAmple ∧
      Nonempty ((L'.pullback η[C].left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Spec (.of K))) ∧
      Nonempty (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule
          (Q.pullback (ProductFiberMaps.productFiberMap A.scheme A.scheme z ≫ (p.hom ⊗ₘ 𝟙 A.scheme).left)).sheaf
          (L'.pullback (fst C C).left).sheaf)
        (L'.pullback (snd C C).left).sheaf ≅ (L'.pullback μ[C].left).sheaf) := by
  let L' := L.pullback (Limits.pullback.fst A.scheme.hom z)
  exact ⟨L', FiberAmpleness.ample_on_geometric_fiber A L hL K z,
    LineBundleFieldTriviality.lineBundle_over_field_trivial K (L'.pullback η[(A.pullback z).scheme].left),
    ⟨quotientDifference_fiberFormulaIso p L Q recover K z⟩⟩

end

end OAI.RepresentationTheory.Theta.Geometric.QuotientDifferenceFibers
