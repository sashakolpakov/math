import OAI.RepresentationTheory.Theta.Geometric.IsogenyKernelScheme
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.ComplexLevel

/-! # Isogeny Kernel Labels -/

namespace OAI.RepresentationTheory.Theta.Geometric.IsogenyKernelLabels

noncomputable section

/-! Complex labels of a finite etale isogeny kernel determine its
constant group functor on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {g h : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
  (p : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) [Etale p.hom.left]

theorem exists_isogenyKernel_labelIso (G : Type) [Group G]
    (labels : G ≃* p.kernelAt (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) :
    Nonempty (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase G ≅ IsogenyKernelScheme.isogenyKernelFunctor p) := by
  obtain ⟨H, hH, hfinite, ⟨e⟩⟩ :=
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Geometric.Splitting.GeometricSplitting.exists_constant_groupIso (IsogenyKernelScheme.isogenyKernelScheme p)
  let : Group H := hH
  let : Finite H := hfinite
  let e' : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase H ≅ IsogenyKernelScheme.isogenyKernelFunctor p :=
    e ≪≫ IsogenyKernelScheme.isogenyKernelYonedaIso p
  let ep : H ≃* p.kernelAt (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) :=
    (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.ComplexLevel.constantValuesEquiv H).trans
      ((e'.app (.op (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))).groupIsoToMulEquiv)
  exact ⟨AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupIsomorphisms.constantGroupIsoOfLabels (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase (labels.trans ep.symm)) ≪≫ e'⟩

def fieldConstantValuesEquiv (F : Type) [Field F] (G : Type) [Group G] :
    G ≃* LocallyConstant (Spec (.of F)) G where
  toFun := LocallyConstant.const _
  invFun f := f default
  left_inv _ := rfl
  right_inv f := by
    apply LocallyConstant.ext
    intro x
    exact congrArg f (Subsingleton.elim default x)
  map_mul' _ _ := rfl

theorem isogenyKernel_geometric_labels (G : Type) [Group G]
    (labels : G ≃* p.kernelAt (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) (F : Type) [Field F]
    (s : Spec (.of F) ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) : Nonempty (G ≃* p.kernelAt (Over.mk s)) := by
  obtain ⟨e⟩ := exists_isogenyKernel_labelIso p G labels
  exact ⟨(fieldConstantValuesEquiv F G).trans ((e.app (.op (Over.mk s))).groupIsoToMulEquiv)⟩

end

end OAI.RepresentationTheory.Theta.Geometric.IsogenyKernelLabels
