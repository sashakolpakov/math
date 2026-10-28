import OAI.RepresentationTheory.Theta.Geometric.IsogenyKernelLabels

/-! # Kernel Label Fibers -/

namespace OAI.RepresentationTheory.Theta.Geometric.KernelLabelFibers

noncomputable section

/-! A kernel label trivialization identifies the actual kernel-valued
map on each of its open label fibers, over every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {g h : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (p : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) {G : Type} [Group G]
    (e : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.GroupMaps.constantGroupFunctor AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase G ≅ IsogenyKernelScheme.isogenyKernelFunctor p)

def kernelLabelFunction {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (k : p.kernelAt T) : LocallyConstant T.left G :=
  e.inv.app (.op T) k

def kernelLabelPoint (a : G) : p.kernelAt (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) :=
  e.hom.app (.op (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase a)

theorem kernelLabelFunction_pullback {T U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (j : U ⟶ T) (k : p.kernelAt T) :
    kernelLabelFunction p e (IsogenyKernelScheme.isogenyKernelPullback p j k) =
      (kernelLabelFunction p e k).comap ⟨j.left, j.left.continuous⟩ :=
  ConcreteCategory.congr_hom (e.inv.naturality j.op) k

theorem kernelLabelFunction_mul {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (k l : p.kernelAt T) :
    kernelLabelFunction p e (k * l) = kernelLabelFunction p e k * kernelLabelFunction p e l :=
  (e.inv.app (.op T)).hom.map_mul k l

theorem kernelLabelPoint_mul (a b : G) :
    (kernelLabelPoint p e (a * b)).val = (kernelLabelPoint p e a).val * (kernelLabelPoint p e b).val :=
  congrArg Subtype.val ((e.hom.app (.op (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))).hom.map_mul
    (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase a) (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase b))

theorem kernelLabelFunction_fiber {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (k : p.kernelAt T) (a : G) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.fiberInclusion T (kernelLabelFunction p e k) a ≫ k.val =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.toBase (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.fiberTest T (kernelLabelFunction p e k) a) ≫ (kernelLabelPoint p e a).val := by
  let c := kernelLabelFunction p e k
  let U := AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.fiberTest T c a
  let j := AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.fiberInclusion T c a
  have hc : c.comap ⟨j.left, j.left.continuous⟩ = LocallyConstant.const U.left a := by
    apply LocallyConstant.ext
    intro x
    exact x.property
  have he : e.hom.app (.op T) c = k := ConcreteCategory.congr_hom (e.inv_hom_id_app (.op T)) k
  have hj := ConcreteCategory.congr_hom (e.hom.naturality j.op) c
  change e.hom.app (.op U) (c.comap ⟨j.left, j.left.continuous⟩) =
    IsogenyKernelScheme.isogenyKernelPullback p j (e.hom.app (.op T) c) at hj
  rw [hc, he] at hj
  have hb := ConcreteCategory.congr_hom (e.hom.naturality (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.toBase U).op)
    (LocallyConstant.const AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase a)
  change e.hom.app (.op U) (LocallyConstant.const U.left a) =
    IsogenyKernelScheme.isogenyKernelPullback p (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.toBase U) (kernelLabelPoint p e a) at hb
  exact congrArg Subtype.val (hj.symm.trans hb)

end

end OAI.RepresentationTheory.Theta.Geometric.KernelLabelFibers
