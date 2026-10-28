import OAI.RepresentationTheory.Theta.Geometric.KernelTransportNaturality
import OAI.RepresentationTheory.Theta.Geometric.LocallyTranslatedIsoComposition

/-! # Kernel Transport Composition -/

namespace OAI.RepresentationTheory.Theta.Geometric.KernelTransportComposition

noncomputable section

section

/-! Composition of the actual kernel transports on arbitrary test
schemes follows from the normalized label comparisons. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

theorem firstKernelTranslate_mul {S : Scheme} (A : Over S) [GrpObj A] {T : Over S}
    (x : T ⟶ A ⊗ A) (k l : T ⟶ A) :
    KernelDifferenceTransport.firstKernelTranslate A (KernelDifferenceTransport.firstKernelTranslate A x k) l = KernelDifferenceTransport.firstKernelTranslate A x (k * l) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp only [KernelDifferenceTransport.firstKernelTranslate, lift_fst, lift_snd, mul_assoc]

variable {g h : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (p : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) {G : Type} [Group G]
    (labels : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase G ≅ IsogenyKernelScheme.isogenyKernelFunctor p)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (hL : ∀ a : p.kernelAt (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase),
      Nonempty ((L.pullback (DifferenceBundleTranslation.groupTranslation A.scheme a.val).left).sheaf ≅ L.sheaf))
    (e : ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback
      (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left)

def kernelDifferenceLabelTranslation (a : G) : (A.scheme ⊗ A.scheme).left ⟶ (A.scheme ⊗ A.scheme).left :=
  (DifferenceBundleTranslation.groupTranslation A.scheme (KernelLabelFibers.kernelLabelPoint p labels a).val ⊗ₘ 𝟙 A.scheme).left

theorem kernelDifferenceLabelTranslation_comp (a b : G) :
    kernelDifferenceLabelTranslation p labels a ≫ kernelDifferenceLabelTranslation p labels b =
      kernelDifferenceLabelTranslation p labels (a * b) := by
  have h := DifferenceBundleTranslation.firstTranslation_comp A.scheme (KernelLabelFibers.kernelLabelPoint p labels a).val (KernelLabelFibers.kernelLabelPoint p labels b).val
  rw [← KernelLabelFibers.kernelLabelPoint_mul p labels a b] at h
  exact congrArg Over.Hom.left h

theorem kernelDifferenceLabelIso_comp (a b : G) :
    ((Scheme.Modules.pullbackCongr (kernelDifferenceLabelTranslation_comp p labels a b)).app
        (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf).symm ≪≫
      Normalized.PullbackComposition.composePullbackIso (kernelDifferenceLabelTranslation p labels a) (kernelDifferenceLabelTranslation p labels b)
        (KernelDifferenceTransport.kernelDifferenceLabelIso p labels L hL e a) (KernelDifferenceTransport.kernelDifferenceLabelIso p labels L hL e b) =
      KernelDifferenceTransport.kernelDifferenceLabelIso p labels L hL e (a * b) :=
  DifferenceTranslationCocycle.normalizedDifferenceTranslation_comp_eq A L e (KernelLabelFibers.kernelLabelPoint p labels a).val
    (KernelLabelFibers.kernelLabelPoint p labels b).val (KernelLabelFibers.kernelLabelPoint p labels (a * b)).val
    (KernelLabelFibers.kernelLabelPoint_mul p labels a b).symm (hL _) (hL _) (hL _)
    (kernelDifferenceLabelTranslation_comp p labels a b)

theorem kernelDifferenceTransportToIso_comp {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (x y z : T ⟶ A.scheme ⊗ A.scheme) (k l : p.kernelAt T)
    (hy : y = KernelDifferenceTransport.firstKernelTranslate A.scheme x k.val)
    (hz : z = KernelDifferenceTransport.firstKernelTranslate A.scheme y l.val)
    (hxz : z = KernelDifferenceTransport.firstKernelTranslate A.scheme x (k * l).val) :
    (KernelTransportNaturality.kernelDifferenceTransportToIso p labels L hL e y z l hz).hom ≫
      (KernelTransportNaturality.kernelDifferenceTransportToIso p labels L hL e x y k hy).hom =
        (KernelTransportNaturality.kernelDifferenceTransportToIso p labels L hL e x z (k * l) hxz).hom := by
  let c := KernelLabelFibers.kernelLabelFunction p labels k
  let d := KernelLabelFibers.kernelLabelFunction p labels l
  have hcd : KernelLabelFibers.kernelLabelFunction p labels (k * l) = c * d := KernelLabelFibers.kernelLabelFunction_mul p labels k l
  have h₃ : ∀ a, (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (c * d) a).ι ≫ z.left =
      ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (c * d) a).ι ≫ x.left) ≫ kernelDifferenceLabelTranslation p labels a := by
    rw [← hcd]
    exact KernelTransportNaturality.kernelDifference_target_fiber_eq p labels x z (k * l) hxz
  apply LocallyTranslatedIsoComposition.locallyTranslatedIso_comp (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf
    (kernelDifferenceLabelTranslation p labels) (kernelDifferenceLabelTranslation_comp p labels)
    (KernelDifferenceTransport.kernelDifferenceLabelIso p labels L hL e) (kernelDifferenceLabelIso_comp p labels L hL e)
    c d x.left y.left z.left
    (KernelTransportNaturality.kernelDifference_target_fiber_eq p labels x y k hy)
    (KernelTransportNaturality.kernelDifference_target_fiber_eq p labels y z l hz) h₃
  · exact KernelTransportNaturality.kernelDifferenceTransportToIso_restrict p labels L hL e x y k hy
  · exact KernelTransportNaturality.kernelDifferenceTransportToIso_restrict p labels L hL e y z l hz
  · intro a
    revert h₃
    rw [← hcd]
    intro h₃
    exact KernelTransportNaturality.kernelDifferenceTransportToIso_restrict p labels L hL e x z (k * l) hxz a

end

/-! Invertibility and the proved composition law force identity
transport at the identity kernel point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

theorem firstKernelTranslate_one {S : Scheme} (A : Over S) [GrpObj A] {T : Over S}
    (x : T ⟶ A ⊗ A) : KernelDifferenceTransport.firstKernelTranslate A x 1 = x := by
  apply CartesianMonoidalCategory.hom_ext <;> simp only [KernelDifferenceTransport.firstKernelTranslate, lift_fst, lift_snd, mul_one]

variable {g h : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (p : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) {G : Type} [Group G]
    (labels : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase G ≅ IsogenyKernelScheme.isogenyKernelFunctor p)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (hL : ∀ a : p.kernelAt (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase),
      Nonempty ((L.pullback (DifferenceBundleTranslation.groupTranslation A.scheme a.val).left).sheaf ≅ L.sheaf))
    (e : ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback
      (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left)

theorem kernelDifferenceTransportToIso_self {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (x : T ⟶ A.scheme ⊗ A.scheme) (k : p.kernelAt T) (hk : k = 1)
    (hx : x = KernelDifferenceTransport.firstKernelTranslate A.scheme x k.val) :
    KernelTransportNaturality.kernelDifferenceTransportToIso p labels L hL e x x k hx = Iso.refl _ := by
  subst k
  have hc := kernelDifferenceTransportToIso_comp p labels L hL e x x x 1 1 hx hx (by simpa only [one_mul] using hx)
  have hc' : (KernelTransportNaturality.kernelDifferenceTransportToIso p labels L hL e x x 1 hx).hom ≫
      (KernelTransportNaturality.kernelDifferenceTransportToIso p labels L hL e x x 1 hx).hom =
      (KernelTransportNaturality.kernelDifferenceTransportToIso p labels L hL e x x 1 hx).hom := by
    simpa only [one_mul] using hc
  apply Iso.ext
  exact (cancel_epi (KernelTransportNaturality.kernelDifferenceTransportToIso p labels L hL e x x 1 hx).hom).mp
    (hc'.trans (Category.comp_id _).symm)

theorem kernelDifferenceTransportToIso_comp_eq {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (x y z : T ⟶ A.scheme ⊗ A.scheme) (k l m : p.kernelAt T) (hm : k * l = m)
    (hy : y = KernelDifferenceTransport.firstKernelTranslate A.scheme x k.val)
    (hz : z = KernelDifferenceTransport.firstKernelTranslate A.scheme y l.val)
    (hxz : z = KernelDifferenceTransport.firstKernelTranslate A.scheme x m.val) :
    KernelTransportNaturality.kernelDifferenceTransportToIso p labels L hL e y z l hz ≪≫
      KernelTransportNaturality.kernelDifferenceTransportToIso p labels L hL e x y k hy =
        KernelTransportNaturality.kernelDifferenceTransportToIso p labels L hL e x z m hxz := by
  subst m
  exact Iso.ext (kernelDifferenceTransportToIso_comp p labels L hL e x y z k l hy hz hxz)

end

end OAI.RepresentationTheory.Theta.Geometric.KernelTransportComposition
