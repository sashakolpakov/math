import OAI.RepresentationTheory.Theta.Geometric.ProductFiberNaturality
import OAI.RepresentationTheory.Theta.Geometric.QuotientDifferenceFibers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData

/-! # Positive Difference -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PositiveDifference

noncomputable section

/-! Once a native Poincare bundle has the actual ample difference
pullback, the native geometric-fiber positivity condition follows. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

variable {g : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (D : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
    (p : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A D.abelian)

theorem polarizationFiberMap_eq {T : Scheme} (z : T ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) :
    (((Over.pullback z).map p.hom ⊗ₘ 𝟙 (A.pullback z).scheme).left ≫ AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.poincareBaseChangeMap D z) =
      ProductFiberMaps.productFiberMap A.scheme A.scheme z ≫ (p.hom ⊗ₘ 𝟙 A.scheme).left := by
  have H := ProductFiberNaturality.productFiberMap_naturality p.hom (𝟙 A.scheme) z
  rw [(Over.pullback z).map_id A.scheme] at H
  exact H.symm

theorem positiveOnGeometricFiber_of_difference_iso
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) (hL : L.IsAmple)
    (recover : (D.poincare.pullback (p.hom ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
      (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf)
    (K : Type) [Field K] [IsAlgClosed K] (z : Spec (.of K) ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PositiveOnGeometricFiber D p.hom K z := by
  obtain ⟨L', hamp, hzero, ⟨hf⟩⟩ := QuotientDifferenceFibers.quotientDifference_positive_fiber p L D.poincare recover hL K z
  refine ⟨L', hamp, hzero, ⟨?_⟩⟩
  exact AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCongr ((Scheme.Modules.pullbackCongr (polarizationFiberMap_eq D p z)).app D.poincare.sheaf)
      (Iso.refl _)) (Iso.refl _) ≪≫ hf

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PositiveDifference
