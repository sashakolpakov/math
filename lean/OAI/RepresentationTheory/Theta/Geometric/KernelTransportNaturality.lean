import OAI.RepresentationTheory.Theta.Geometric.KernelDifferenceTransport
import OAI.RepresentationTheory.Theta.Geometric.LocallyTranslatedIsoNaturality

/-! # Kernel Transport Naturality -/

namespace OAI.RepresentationTheory.Theta.Geometric.KernelTransportNaturality

noncomputable section

section

/-! The actual kernel transport, chosen by its exact local formulas,
commutes with every change of test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations

theorem firstKernelTranslate_natural {S : Scheme} (A : Over S) [GrpObj A]
    {T U : Over S} (x : T ⟶ A ⊗ A) (k : T ⟶ A) (j : U ⟶ T) :
    j ≫ KernelDifferenceTransport.firstKernelTranslate A x k = KernelDifferenceTransport.firstKernelTranslate A (j ≫ x) (j ≫ k) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [KernelDifferenceTransport.firstKernelTranslate, Category.assoc, lift_fst, lift_snd, MonObj.comp_mul]

variable {g h : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (p : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) {G : Type} [Group G]
    (labels : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase G ≅ IsogenyKernelScheme.isogenyKernelFunctor p)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (hL : ∀ a : p.kernelAt (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase),
      Nonempty ((L.pullback (DifferenceBundleTranslation.groupTranslation A.scheme a.val).left).sheaf ≅ L.sheaf))
    (e : ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback
      (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left)

def kernelDifferenceTransportIso {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (x : T ⟶ A.scheme ⊗ A.scheme) (k : p.kernelAt T) :
    ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback (KernelDifferenceTransport.firstKernelTranslate A.scheme x k.val).left).sheaf ≅
      ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback x.left).sheaf :=
  (KernelDifferenceTransport.exists_kernelDifferenceTransport p labels L hL e x k).choose

theorem kernelDifferenceTransportIso_restrict {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (x : T ⟶ A.scheme ⊗ A.scheme) (k : p.kernelAt T) (a : G) :
    (Scheme.Modules.pullback (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (KernelLabelFibers.kernelLabelFunction p labels k) a).ι).map
        (kernelDifferenceTransportIso p labels L hL e x k).hom =
      (LocallyTranslatedLineIso.restrictedTranslatedMapLineIso (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf
        (DifferenceBundleTranslation.groupTranslation A.scheme (KernelLabelFibers.kernelLabelPoint p labels a).val ⊗ₘ 𝟙 A.scheme).left
        (KernelDifferenceTransport.kernelDifferenceLabelIso p labels L hL e a) x.left (KernelDifferenceTransport.firstKernelTranslate A.scheme x k.val).left
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (KernelLabelFibers.kernelLabelFunction p labels k) a)
        (KernelDifferenceTransport.kernelDifference_fiber_eq p labels x k a)).hom :=
  (KernelDifferenceTransport.exists_kernelDifferenceTransport p labels L hL e x k).choose_spec a

theorem kernelDifferenceTransportIso_naturality {T U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (x : T ⟶ A.scheme ⊗ A.scheme) (k : p.kernelAt T) (j : U ⟶ T) :
    AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.nativePullback (kernelDifferenceTransportIso p labels L hL e x k).hom j.left
      (KernelDifferenceTransport.firstKernelTranslate A.scheme (j ≫ x) (IsogenyKernelScheme.isogenyKernelPullback p j k).val).left (j ≫ x).left
      (congrArg Over.Hom.left (firstKernelTranslate_natural A.scheme x k.val j)) rfl =
        (kernelDifferenceTransportIso p labels L hL e (j ≫ x) (IsogenyKernelScheme.isogenyKernelPullback p j k)).hom := by
  apply LocallyTranslatedIsoNaturality.locallyTranslatedIso_naturality (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf _
    (KernelDifferenceTransport.kernelDifferenceLabelIso p labels L hL e)
    (KernelLabelFibers.kernelLabelFunction p labels k) (KernelLabelFibers.kernelLabelFunction p labels (IsogenyKernelScheme.isogenyKernelPullback p j k)) j.left
    (fun u => congrArg (fun c : LocallyConstant U.left G => c u) (KernelLabelFibers.kernelLabelFunction_pullback p labels j k))
    x.left (KernelDifferenceTransport.firstKernelTranslate A.scheme x k.val).left (j ≫ x).left
    (KernelDifferenceTransport.firstKernelTranslate A.scheme (j ≫ x) (IsogenyKernelScheme.isogenyKernelPullback p j k).val).left
    rfl (congrArg Over.Hom.left (firstKernelTranslate_natural A.scheme x k.val j))
    (KernelDifferenceTransport.kernelDifference_fiber_eq p labels x k)
    (KernelDifferenceTransport.kernelDifference_fiber_eq p labels (j ≫ x) (IsogenyKernelScheme.isogenyKernelPullback p j k))
  · exact kernelDifferenceTransportIso_restrict p labels L hL e x k
  · exact kernelDifferenceTransportIso_restrict p labels L hL e (j ≫ x) (IsogenyKernelScheme.isogenyKernelPullback p j k)

end

/-! Kernel transport with an explicitly specified target map, retaining
its exact label-fiber formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations

variable {g h : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (p : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) {G : Type} [Group G]
    (labels : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase G ≅ IsogenyKernelScheme.isogenyKernelFunctor p)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (hL : ∀ a : p.kernelAt (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase),
      Nonempty ((L.pullback (DifferenceBundleTranslation.groupTranslation A.scheme a.val).left).sheaf ≅ L.sheaf))
    (e : ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback
      (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left)

def kernelDifferenceTransportToIso {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (x y : T ⟶ A.scheme ⊗ A.scheme) (k : p.kernelAt T)
    (hy : y = KernelDifferenceTransport.firstKernelTranslate A.scheme x k.val) :
    ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback y.left).sheaf ≅
      ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback x.left).sheaf :=
  (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hy)).app (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf ≪≫
    kernelDifferenceTransportIso p labels L hL e x k

theorem kernelDifference_target_fiber_eq {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (x y : T ⟶ A.scheme ⊗ A.scheme) (k : p.kernelAt T)
    (hy : y = KernelDifferenceTransport.firstKernelTranslate A.scheme x k.val) (a : G) :
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (KernelLabelFibers.kernelLabelFunction p labels k) a).ι ≫ y.left =
      ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (KernelLabelFibers.kernelLabelFunction p labels k) a).ι ≫ x.left) ≫
        (DifferenceBundleTranslation.groupTranslation A.scheme (KernelLabelFibers.kernelLabelPoint p labels a).val ⊗ₘ 𝟙 A.scheme).left := by
  subst y
  exact KernelDifferenceTransport.kernelDifference_fiber_eq p labels x k a

theorem kernelDifferenceTransportToIso_restrict {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (x y : T ⟶ A.scheme ⊗ A.scheme) (k : p.kernelAt T)
    (hy : y = KernelDifferenceTransport.firstKernelTranslate A.scheme x k.val) (a : G) :
    (Scheme.Modules.pullback (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (KernelLabelFibers.kernelLabelFunction p labels k) a).ι).map
        (kernelDifferenceTransportToIso p labels L hL e x y k hy).hom =
      (LocallyTranslatedLineIso.restrictedTranslatedMapLineIso (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf
        (DifferenceBundleTranslation.groupTranslation A.scheme (KernelLabelFibers.kernelLabelPoint p labels a).val ⊗ₘ 𝟙 A.scheme).left
        (KernelDifferenceTransport.kernelDifferenceLabelIso p labels L hL e a) x.left y.left
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (KernelLabelFibers.kernelLabelFunction p labels k) a)
        (kernelDifference_target_fiber_eq p labels x y k hy a)).hom := by
  subst y
  exact kernelDifferenceTransportIso_restrict p labels L hL e x k a

theorem kernelDifferenceTransportToIso_naturality {T U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (x y : T ⟶ A.scheme ⊗ A.scheme) (k : p.kernelAt T)
    (hy : y = KernelDifferenceTransport.firstKernelTranslate A.scheme x k.val) (j : U ⟶ T)
    (x' y' : U ⟶ A.scheme ⊗ A.scheme) (k' : p.kernelAt U)
    (hx' : j ≫ x = x') (hy' : j ≫ y = y') (hk' : IsogenyKernelScheme.isogenyKernelPullback p j k = k')
    (h' : y' = KernelDifferenceTransport.firstKernelTranslate A.scheme x' k'.val) :
    AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.nativePullback (kernelDifferenceTransportToIso p labels L hL e x y k hy).hom j.left
      y'.left x'.left (congrArg Over.Hom.left hy') (congrArg Over.Hom.left hx') =
        (kernelDifferenceTransportToIso p labels L hL e x' y' k' h').hom := by
  subst x'
  subst y'
  subst k'
  apply LocallyTranslatedIsoNaturality.locallyTranslatedIso_naturality (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf _
    (KernelDifferenceTransport.kernelDifferenceLabelIso p labels L hL e)
    (KernelLabelFibers.kernelLabelFunction p labels k) (KernelLabelFibers.kernelLabelFunction p labels (IsogenyKernelScheme.isogenyKernelPullback p j k)) j.left
    (fun u => congrArg (fun c : LocallyConstant U.left G => c u) (KernelLabelFibers.kernelLabelFunction_pullback p labels j k))
    x.left y.left (j ≫ x).left (j ≫ y).left rfl rfl
    (kernelDifference_target_fiber_eq p labels x y k hy)
    (kernelDifference_target_fiber_eq p labels (j ≫ x) (j ≫ y) (IsogenyKernelScheme.isogenyKernelPullback p j k) h')
  · exact kernelDifferenceTransportToIso_restrict p labels L hL e x y k hy
  · exact kernelDifferenceTransportToIso_restrict p labels L hL e (j ≫ x) (j ≫ y) (IsogenyKernelScheme.isogenyKernelPullback p j k) h'

end

end OAI.RepresentationTheory.Theta.Geometric.KernelTransportNaturality
