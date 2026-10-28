import OAI.RepresentationTheory.Theta.Geometric.ProductKernelCoordinates
import OAI.RepresentationTheory.Theta.Geometric.KernelTransportComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentReindexing

/-! # Difference Kernel Linearization -/

namespace OAI.RepresentationTheory.Theta.Geometric.DifferenceKernelLinearization

noncomputable section

/-! The normalized difference transport defines a genuine kernel
linearization, with its unit, composition, and all-test pullback laws. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations
attribute [local instance] AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelGroup

theorem overPullHom_eq_native {S : Scheme} {X Y T U : Over S}
    {M : X.left.Modules} {N : Y.left.Modules} {x : T ⟶ X} {y : T ⟶ Y}
    (φ : (Scheme.Modules.pullback x.left).obj M ⟶ (Scheme.Modules.pullback y.left).obj N)
    (j : U ⟶ T) (x' : U ⟶ X) (y' : U ⟶ Y) (hx : j ≫ x = x') (hy : j ≫ y = y') :
    pullHom (F := AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks S) φ j x' y' hx hy =
      AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.nativePullback φ j.left x'.left y'.left (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) :=
  (AlgebraicGeometry.Picard.PoincareBundle.DescentReindexing.pullHom_reindex (Over.forget S) AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks φ j x' y' hx hy).trans
    (AlgebraicGeometry.Picard.PoincareBundle.Geometric.PullHom.pullHom_eq φ j.left x'.left y'.left _ _)

variable {g h : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (p : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) {G : Type} [Group G]
    (labels : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase G ≅ IsogenyKernelScheme.isogenyKernelFunctor p)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (hL : ∀ a : p.kernelAt (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase),
      Nonempty ((L.pullback (DifferenceBundleTranslation.groupTranslation A.scheme a.val).left).sheaf ≅ L.sheaf))
    (e : ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback
      (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left)

def differenceKernelTransportIso {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (x y : T ⟶ A.scheme ⊗ A.scheme)
    (k : T ⟶ AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelObject (p.hom ⊗ₘ 𝟙 A.scheme))
    (hk : x * (k ≫ AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (p.hom ⊗ₘ 𝟙 A.scheme)) = y) :
    ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback y.left).sheaf ≅
      ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback x.left).sheaf :=
  KernelTransportNaturality.kernelDifferenceTransportToIso p labels L hL e x y (ProductKernelCoordinates.productKernelFirst p T k)
    (hk.symm.trans (ProductKernelCoordinates.productKernel_translate p x k))

def differenceKernelLinearization :
    AlgebraicGeometry.Picard.PoincareBundle.Kernel.Linearization.KernelLinearization (p.hom ⊗ₘ 𝟙 A.scheme)
      (AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf where
  transport {_T} x y k hk := (differenceKernelTransportIso p labels L hL e x y k hk).inv
  unit_compat {T} x hx := by
    have hi := KernelTransportComposition.kernelDifferenceTransportToIso_self p labels L hL e x (ProductKernelCoordinates.productKernelFirst p T 1)
      (map_one (ProductKernelCoordinates.productKernelFirst p T)) (hx.symm.trans (ProductKernelCoordinates.productKernel_translate p x 1))
    exact congrArg Iso.inv hi
  mul_compat {T} x y z k l m hx hy hz hm := by
    have hm' : ProductKernelCoordinates.productKernelFirst p T k * ProductKernelCoordinates.productKernelFirst p T l = ProductKernelCoordinates.productKernelFirst p T m :=
      ((ProductKernelCoordinates.productKernelFirst p T).map_mul k l).symm.trans (congrArg (ProductKernelCoordinates.productKernelFirst p T) hm)
    have hi := KernelTransportComposition.kernelDifferenceTransportToIso_comp_eq p labels L hL e x y z
      (ProductKernelCoordinates.productKernelFirst p T k) (ProductKernelCoordinates.productKernelFirst p T l) (ProductKernelCoordinates.productKernelFirst p T m) hm'
      (hx.symm.trans (ProductKernelCoordinates.productKernel_translate p x k))
      (hy.symm.trans (ProductKernelCoordinates.productKernel_translate p y l))
      (hz.symm.trans (ProductKernelCoordinates.productKernel_translate p x m))
    exact congrArg Iso.inv hi
  pullback_compat {T U} j x y k hk x' y' k' hk' hx hy hkk := by
    have hkernel : IsogenyKernelScheme.isogenyKernelPullback p j (ProductKernelCoordinates.productKernelFirst p T k) = ProductKernelCoordinates.productKernelFirst p U k' :=
      (ProductKernelCoordinates.productKernelFirst_natural p j k).trans (congrArg (ProductKernelCoordinates.productKernelFirst p U) hkk)
    have hn := KernelTransportNaturality.kernelDifferenceTransportToIso_naturality p labels L hL e x y (ProductKernelCoordinates.productKernelFirst p T k)
      (hk.symm.trans (ProductKernelCoordinates.productKernel_translate p x k)) j x' y' (ProductKernelCoordinates.productKernelFirst p U k') hx hy hkernel
      (hk'.symm.trans (ProductKernelCoordinates.productKernel_translate p x' k'))
    have hi : AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition.pullIso (AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.overModulePullbacks AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)
        (differenceKernelTransportIso p labels L hL e x y k hk) j y' x' hy hx =
          differenceKernelTransportIso p labels L hL e x' y' k' hk' := by
      apply Iso.ext
      exact (overPullHom_eq_native _ j y' x' hy hx).trans hn
    exact congrArg Iso.inv hi

end

end OAI.RepresentationTheory.Theta.Geometric.DifferenceKernelLinearization
