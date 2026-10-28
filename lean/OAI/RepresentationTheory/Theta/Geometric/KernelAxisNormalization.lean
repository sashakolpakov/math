import OAI.RepresentationTheory.Theta.Geometric.Local.NormalizedFrames
import OAI.RepresentationTheory.Theta.Geometric.KernelTransportNaturality

/-! # Kernel Axis Normalization -/

namespace OAI.RepresentationTheory.Theta.Geometric.KernelAxisNormalization

noncomputable section

/-! The all-test kernel transport preserves the original zero-axis
normalization, before descending that normalization to the quotient. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations

variable {g h : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (p : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) {G : Type} [Group G]
    (labels : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase G ≅ IsogenyKernelScheme.isogenyKernelFunctor p)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (hL : ∀ a : p.kernelAt (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase),
      Nonempty ((L.pullback (DifferenceBundleTranslation.groupTranslation A.scheme a.val).left).sheaf ≅ L.sheaf))
    (e : ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback
      (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left)

theorem kernel_axis_fiber_translation {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (v w : T ⟶ A.scheme)
    (k : p.kernelAt T) (hw : w = v * k.val) (a : G) :
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (KernelLabelFibers.kernelLabelFunction p labels k) a).ι ≫ w.left =
      ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (KernelLabelFibers.kernelLabelFunction p labels k) a).ι ≫ v.left) ≫
        (DifferenceBundleTranslation.groupTranslation A.scheme (KernelLabelFibers.kernelLabelPoint p labels a).val).left := by
  let j := AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.fiberInclusion T (KernelLabelFibers.kernelLabelFunction p labels k) a
  have h : j ≫ w = (j ≫ v) ≫ DifferenceBundleTranslation.groupTranslation A.scheme (KernelLabelFibers.kernelLabelPoint p labels a).val := by
    rw [hw, MonObj.comp_mul, DifferenceBundleTranslation.groupTranslation_comp, KernelLabelFibers.kernelLabelFunction_fiber]
    congr 2
    exact Over.mkIdTerminal.hom_ext _ _
  exact congrArg Over.Hom.left h

theorem kernelDifferenceTransportToIso_axis {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (v w : T ⟶ A.scheme)
    (k : p.kernelAt T) (hw : w = v * k.val)
    (hy : w ≫ lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme) =
      KernelDifferenceTransport.firstKernelTranslate A.scheme (v ≫ lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)) k.val) :
    (KernelTransportNaturality.kernelDifferenceTransportToIso p labels L hL e
      (v ≫ lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme))
      (w ≫ lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)) k hy).hom ≫
        (FactoredPullbackFrames.factoredPullbackFrame v.left (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left e).hom =
      (FactoredPullbackFrames.factoredPullbackFrame w.left (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left e).hom := by
  apply Local.NormalizedFrames.locallyTranslatedIso_axis_frame (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf
    (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left e
    (fun a => (DifferenceBundleTranslation.groupTranslation A.scheme (KernelLabelFibers.kernelLabelPoint p labels a).val ⊗ₘ 𝟙 A.scheme).left)
    (fun a => (DifferenceBundleTranslation.groupTranslation A.scheme (KernelLabelFibers.kernelLabelPoint p labels a).val).left)
    (fun a => (congrArg Over.Hom.left
      (DifferenceBundleTranslation.firstTranslation_zeroSlice A.scheme (KernelLabelFibers.kernelLabelPoint p labels a).val)).symm)
    (KernelDifferenceTransport.kernelDifferenceLabelIso p labels L hL e)
    (fun a => DifferenceTranslationCocycle.normalizedDifferenceTranslation_normalized A L e
      (KernelLabelFibers.kernelLabelPoint p labels a).val (hL _))
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (KernelLabelFibers.kernelLabelFunction p labels k)) (by
      apply top_unique
      intro t _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨KernelLabelFibers.kernelLabelFunction p labels k t, rfl⟩)
    v.left w.left (kernel_axis_fiber_translation p labels v w k hw)
    (KernelTransportNaturality.kernelDifference_target_fiber_eq p labels _ _ k hy)
  exact KernelTransportNaturality.kernelDifferenceTransportToIso_restrict p labels L hL e _ _ k hy

end

end OAI.RepresentationTheory.Theta.Geometric.KernelAxisNormalization
