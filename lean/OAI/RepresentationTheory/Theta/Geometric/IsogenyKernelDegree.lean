import OAI.RepresentationTheory.Theta.Geometric.IsogenyKernelLabels
import OAI.RepresentationTheory.Theta.Geometric.ConstantSchemeDegree

/-! # Isogeny Kernel Degree -/

namespace OAI.RepresentationTheory.Theta.Geometric.IsogenyKernelDegree

noncomputable section

/-! Finite-flat degree is the cardinality of the actual complex kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections

variable {g h : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
  (p : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) [Etale p.hom.left]

def isogenyKernelLabelSchemeIso (G : Type) [Group G]
    (labels : G ≃* p.kernelAt (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase G ≅ IsogenyKernelScheme.isogenyKernelScheme p :=
  ((AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.BaseChange.constantSetRepresentable AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase G).ofIso
    (Functor.isoWhiskerRight (IsogenyKernelLabels.exists_isogenyKernel_labelIso p G labels).some
      (forget GrpCat))).uniqueUpToIso (IsogenyKernelScheme.isogenyKernelRepresentable p)

theorem isogenyKernelScheme_finrank (G : Type) [Group G] [Finite G]
    (labels : G ≃* p.kernelAt (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) (z : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) :
    (IsogenyKernelScheme.isogenyKernelScheme p).hom.finrank z = Nat.card G := by
  let e := isogenyKernelLabelSchemeIso p G labels
  let : IsIso e.hom.left := inferInstanceAs (IsIso (((Over.forget AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase).mapIso e).hom))
  let : Flat (IsogenyKernelScheme.isogenyKernelScheme p).hom :=
    (Etale.iff_flat_and_formallyUnramified.mp inferInstance).1
  calc
    _ = (e.hom.left ≫ (IsogenyKernelScheme.isogenyKernelScheme p).hom).finrank z := by
      rw [Scheme.Hom.finrank_comp_left_of_isIso]
    _ = (AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Iff.constantScheme AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase G).hom.finrank z :=
      congrArg (fun f => Scheme.Hom.finrank f z) e.hom.w
    _ = Nat.card G := ConstantSchemeDegree.constantScheme_finrank ℂ G z

theorem isogeny_finrank_of_complex_labels [PreconnectedSpace B.scheme.left]
    (G : Type) [Group G] [Finite G] (labels : G ≃* p.kernelAt (AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConstantSectionsOn.ConstantSections.baseTest AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))
    (b : B.scheme.left) : p.hom.left.finrank b = Nat.card G := by
  let z : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase := default
  calc
    _ = p.hom.left.finrank (η[B.scheme].left z) :=
      (Scheme.Hom.isLocallyConstant_finrank p.hom.left).apply_eq_of_preconnectedSpace _ _
    _ = (IsogenyKernelScheme.isogenyKernelScheme p).hom.finrank z :=
      (Scheme.Hom.finrank_pullback_snd p.hom.left η[B.scheme].left z).symm
    _ = Nat.card G := isogenyKernelScheme_finrank p G labels z

end

end OAI.RepresentationTheory.Theta.Geometric.IsogenyKernelDegree
