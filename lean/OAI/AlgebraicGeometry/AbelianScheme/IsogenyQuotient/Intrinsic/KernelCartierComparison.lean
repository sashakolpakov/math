import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RepresentedGroupIsoReflection
import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelGroup

/-! # Kernel Cartier Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.KernelCartierComparison.Construction

noncomputable section

/-! The actual kernel used by character-line descent is canonically
the categorical group kernel, preserving Cartier duality and finite flat geometry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup Picard.PoincareBundle.Kernel.Scheme.kernelGroup_commutative

universe u
variable {S : Scheme.{u}} {A B C Z : Over S}
  [GrpObj A] [GrpObj B] [GrpObj C] [GrpObj Z]
  (f : A ⟶ B) [IsMonHom f] (g : C ⟶ Z) [IsMonHom g]

def nativeKernelGroupIso : Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f) ≅ Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject f) :=
  Grp.mkIso' (Picard.Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso f)

omit [GrpObj A] [IsMonHom f] in
theorem categoricalKernel_finiteLocallyFree
    [IsFinite f.left] [Flat f.left] [LocallyOfFinitePresentation f.left] :
    IsFinite (Picard.PoincareBundle.Kernel.Scheme.kernelObject f).hom ∧ Flat (Picard.PoincareBundle.Kernel.Scheme.kernelObject f).hom ∧
      LocallyOfFinitePresentation (Picard.PoincareBundle.Kernel.Scheme.kernelObject f).hom := by
  have h := Picard.Homomorphisms.Kernel.Construction.kernelScheme_finiteLocallyFree f ⟨inferInstance, inferInstance, inferInstance⟩
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom := h.1
  have : Flat (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom := h.2.1
  have : LocallyOfFinitePresentation (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom := h.2.2
  let j := Picard.Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso f
  have : IsIso j.inv.left := (Over.forget S).map_isIso j.inv
  rw [← j.inv.w]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

variable [IsCommMonObj A] [IsCommMonObj C]

def nativeKernelCartierIso
    (Y : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
    (e : CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject g)) ≅
      CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheaf (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S (Grp.mk (Picard.PoincareBundle.Kernel.Scheme.kernelObject f)))) :
    Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme g) ≅ Y.dual := by
  have : IsCommMonObj Y.dual.X := Y.commutative
  exact RepresentedGroupIsoReflection.Construction.groupIsoOfRepresentedFppfAbIso _ _
    (CartierDuality.SheafBaseChange.Construction.Schemes.representedFppfAbIso (nativeKernelGroupIso g) ≪≫ e ≪≫
      (CartierDuality.CommutativeSheavesAb.Construction.Schemes.cartierDualSheafFunctor S).mapIso (CartierDuality.SheafBaseChange.Construction.Schemes.representedFppfAbIso (nativeKernelGroupIso f)).op ≪≫
        Y.representedCartierDualIso.symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.KernelCartierComparison.Construction
