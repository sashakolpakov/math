import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.KernelBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RepresentedGroups

/-! # Base Change Group -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChangeGroup.Construction

noncomputable section

/-! The native kernel base-change isomorphism preserves the actual
group laws. Its group structure is recovered from the embedded inclusion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

attribute [local instance] BaseChange.Construction.pulledBackGroup Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {S T : Scheme.{u}}

theorem isMonHom_of_mono_postcomp {X Y Z : Over S} [GrpObj X] [GrpObj Y] [GrpObj Z]
    (a : X ⟶ Y) (b : Y ⟶ Z) [Mono b] [IsMonHom b] [IsMonHom (a ≫ b)] : IsMonHom a := by
  apply RepresentedGroups.Construction.isMonHom_of_point_operations a
  · intro U
    apply (cancel_mono b).mp
    rw [Category.assoc, MonObj.one_comp, MonObj.one_comp]
  · intro U x y
    apply (cancel_mono b).mp
    rw [Category.assoc, MonObj.mul_comp, MonObj.mul_comp, Category.assoc, Category.assoc]

variable (f : T ⟶ S) {A B : Over S} [GrpObj A] [GrpObj B]
variable (p : A ⟶ B) [IsMonHom p]

instance nativeKernelBaseChangeIso_isMonHom : IsMonHom (KernelBaseChange.Construction.nativeKernelBaseChangeIso f p).hom := by
  have : IsMonHom ((KernelBaseChange.Construction.nativeKernelBaseChangeIso f p).hom ≫
      Picard.PoincareBundle.Kernel.Scheme.kernelInclusion ((Over.pullback f).map p)) := by
    rw [KernelBaseChange.Construction.nativeKernelBaseChangeIso_inclusion]
    infer_instance
  exact isMonHom_of_mono_postcomp (KernelBaseChange.Construction.nativeKernelBaseChangeIso f p).hom
    (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion ((Over.pullback f).map p))

def nativeKernelBaseChangeGroupIso :
    Grp.mk ((Over.pullback f).obj (Picard.PoincareBundle.Kernel.Scheme.kernelObject p)) ≅
      Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject ((Over.pullback f).map p)) :=
  Grp.mkIso' (KernelBaseChange.Construction.nativeKernelBaseChangeIso f p)

theorem nativeKernelBaseChangeGroupIso_inclusion :
    (nativeKernelBaseChangeGroupIso f p).hom.hom.hom ≫
        Picard.PoincareBundle.Kernel.Scheme.kernelInclusion ((Over.pullback f).map p) =
      (Over.pullback f).map (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion p) :=
  KernelBaseChange.Construction.nativeKernelBaseChangeIso_inclusion f p

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChangeGroup.Construction
