import OAI.RepresentationTheory.Theta.Geometric.KernelAxisNormalization
import OAI.RepresentationTheory.Theta.Geometric.DifferenceKernelLinearization

/-! # Difference Axis Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric.DifferenceAxisTransport

noncomputable section

/-! The difference descent action preserves the chosen frame along
the first-coordinate axis on every scheme over the base. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
attribute [local instance] AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {g h : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (p : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) {G : Type} [Group G]
    (labels : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase G ≅ IsogenyKernelScheme.isogenyKernelFunctor p)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (hL : ∀ a : p.kernelAt (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase),
      Nonempty ((L.pullback (DifferenceBundleTranslation.groupTranslation A.scheme a.val).left).sheaf ≅ L.sheaf))
    (e : ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback
      (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left)

theorem productIsogeny_firstZeroSlice :
    lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme) ≫ (p.hom ⊗ₘ 𝟙 A.scheme) =
      p.hom ≫ lift (𝟙 B.scheme) (1 : B.scheme ⟶ A.scheme) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp

theorem productKernel_axis_first {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (v w : T ⟶ A.scheme)
    (k : T ⟶ AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelObject (p.hom ⊗ₘ 𝟙 A.scheme))
    (hk : (v ≫ lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)) *
        (k ≫ AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (p.hom ⊗ₘ 𝟙 A.scheme)) =
      w ≫ lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)) :
    w = v * (ProductKernelCoordinates.productKernelFirst p T k).val := by
  have H := congrArg (fun f => f ≫ fst A.scheme A.scheme) hk
  change w = v * (k ≫ AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (p.hom ⊗ₘ 𝟙 A.scheme) ≫ fst A.scheme A.scheme)
  simpa only [MonObj.mul_comp, Category.assoc, lift_fst, Category.comp_id] using H.symm

theorem differenceKernelTransportIso_axis {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (v w : T ⟶ A.scheme)
    (k : T ⟶ AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelObject (p.hom ⊗ₘ 𝟙 A.scheme))
    (hk : (v ≫ lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)) *
        (k ≫ AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (p.hom ⊗ₘ 𝟙 A.scheme)) =
      w ≫ lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)) :
    (DifferenceKernelLinearization.differenceKernelTransportIso p labels L hL e
      (v ≫ lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme))
      (w ≫ lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)) k hk).inv ≫
        (FactoredPullbackFrames.factoredPullbackFrame w.left (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left e).hom =
      (FactoredPullbackFrames.factoredPullbackFrame v.left (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left e).hom := by
  have H := KernelAxisNormalization.kernelDifferenceTransportToIso_axis p labels L hL e v w
    (ProductKernelCoordinates.productKernelFirst p T k) (productKernel_axis_first p v w k hk)
    (hk.symm.trans (ProductKernelCoordinates.productKernel_translate p _ k))
  apply (cancel_epi (DifferenceKernelLinearization.differenceKernelTransportIso p labels L hL e
    (v ≫ lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme))
    (w ≫ lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)) k hk).hom).mp
  simpa only [DifferenceKernelLinearization.differenceKernelTransportIso, Iso.hom_inv_id_assoc] using H.symm

end

end OAI.RepresentationTheory.Theta.Geometric.DifferenceAxisTransport
