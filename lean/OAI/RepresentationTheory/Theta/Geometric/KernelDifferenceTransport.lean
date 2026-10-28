import OAI.RepresentationTheory.Theta.Geometric.LocallyTranslatedLineIso
import OAI.RepresentationTheory.Theta.Geometric.KernelLabelFibers
import OAI.RepresentationTheory.Theta.Geometric.DifferenceTranslationCocycle

/-! # Kernel Difference Transport -/

namespace OAI.RepresentationTheory.Theta.Geometric.KernelDifferenceTransport

noncomputable section

/-! Actual difference-bundle transport along arbitrary kernel-valued
test maps, glued on the open fibers of the finite etale kernel labels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

def firstKernelTranslate {S : Scheme} (A : Over S) [GrpObj A] {T : Over S}
    (x : T ⟶ A ⊗ A) (k : T ⟶ A) : T ⟶ A ⊗ A :=
  lift ((x ≫ fst A A) * k) (x ≫ snd A A)

theorem firstKernelTranslate_constant {S : Scheme} (A : Over S) [GrpObj A]
    {T U : Over S} (x : T ⟶ A ⊗ A) (k : T ⟶ A) (j : U ⟶ T)
    (p : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest S ⟶ A) (hk : j ≫ k = AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.toBase U ≫ p) :
    j ≫ firstKernelTranslate A x k = (j ≫ x) ≫ (DifferenceBundleTranslation.groupTranslation A p ⊗ₘ 𝟙 A) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [firstKernelTranslate, Category.assoc, lift_fst, MonObj.comp_mul,
      tensorHom_fst]
    change (j ≫ x ≫ fst A A) * (j ≫ k) = (j ≫ x ≫ fst A A) ≫ DifferenceBundleTranslation.groupTranslation A p
    rw [DifferenceBundleTranslation.groupTranslation_comp, hk]
    congr 2
    exact Over.mkIdTerminal.hom_ext _ _
  · simp only [firstKernelTranslate, Category.assoc, lift_snd, tensorHom_snd, Category.comp_id]

variable {g h : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (p : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) {G : Type} [Group G]
    (labels : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase G ≅ IsogenyKernelScheme.isogenyKernelFunctor p)
    (L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (hL : ∀ a : p.kernelAt (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase),
      Nonempty ((L.pullback (DifferenceBundleTranslation.groupTranslation A.scheme a.val).left).sheaf ≅ L.sheaf))
    (e : ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback
      (lift (𝟙 A.scheme) (1 : A.scheme ⟶ A.scheme)).left).sheaf ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.scheme.left)

def kernelDifferenceLabelIso (a : G) :
    ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback
      (DifferenceBundleTranslation.groupTranslation A.scheme (KernelLabelFibers.kernelLabelPoint p labels a).val ⊗ₘ 𝟙 A.scheme).left).sheaf ≅
        (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf :=
  DifferenceTranslationCocycle.normalizedDifferenceTranslation A L e (KernelLabelFibers.kernelLabelPoint p labels a).val (hL _)

theorem kernelDifference_fiber_eq {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (x : T ⟶ A.scheme ⊗ A.scheme) (k : p.kernelAt T) (a : G) :
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (KernelLabelFibers.kernelLabelFunction p labels k) a).ι ≫
        (firstKernelTranslate A.scheme x k.val).left =
      ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (KernelLabelFibers.kernelLabelFunction p labels k) a).ι ≫ x.left) ≫
        (DifferenceBundleTranslation.groupTranslation A.scheme (KernelLabelFibers.kernelLabelPoint p labels a).val ⊗ₘ 𝟙 A.scheme).left :=
  congrArg Over.Hom.left (firstKernelTranslate_constant A.scheme x k.val
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.fiberInclusion T (KernelLabelFibers.kernelLabelFunction p labels k) a) (KernelLabelFibers.kernelLabelPoint p labels a).val
    (KernelLabelFibers.kernelLabelFunction_fiber p labels k a))

theorem exists_kernelDifferenceTransport {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (x : T ⟶ A.scheme ⊗ A.scheme) (k : p.kernelAt T) :
    ∃ d : ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback (firstKernelTranslate A.scheme x k.val).left).sheaf ≅
        ((AbelianDifferenceBundle.abelianDifferenceBundle A L).pullback x.left).sheaf,
      ∀ a, (Scheme.Modules.pullback (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (KernelLabelFibers.kernelLabelFunction p labels k) a).ι).map
          d.hom =
        (LocallyTranslatedLineIso.restrictedTranslatedMapLineIso (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf
          (DifferenceBundleTranslation.groupTranslation A.scheme (KernelLabelFibers.kernelLabelPoint p labels a).val ⊗ₘ 𝟙 A.scheme).left
          (kernelDifferenceLabelIso p labels L hL e a) x.left (firstKernelTranslate A.scheme x k.val).left
          (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.locallyConstantFiber (KernelLabelFibers.kernelLabelFunction p labels k) a)
          (kernelDifference_fiber_eq p labels x k a)).hom :=
  LocallyTranslatedLineIso.exists_iso_of_locally_translated_maps (AbelianDifferenceBundle.abelianDifferenceBundle A L).sheaf
    (KernelLabelFibers.kernelLabelFunction p labels k) _ (kernelDifferenceLabelIso p labels L hL e)
    x.left (firstKernelTranslate A.scheme x k.val).left (kernelDifference_fiber_eq p labels x k)

end

end OAI.RepresentationTheory.Theta.Geometric.KernelDifferenceTransport
