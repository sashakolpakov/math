import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.RelativeAnnihilator
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme

/-! # Morphism Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction

noncomputable section

/-! The original all-test kernel of a native homomorphism is its scheme-theoretic kernel image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u

def nativeMorphismKernel {S : Scheme.{u}} {A B : Over S}
    [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] :
    TorsionQuotient.SubgroupFunctor.RelativeSubgroup A (Over.mk (𝟙 S)) where
  points T _ := (IsMonHom.monoidHom f T).ker
  naturality := by
    intro X Y a t x hx
    change (a ≫ x) ≫ f = 1
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun y => a ≫ y) hx).trans (MonObj.comp_one a))

theorem nativeMorphismKernel_membership {S : Scheme.{u}} {A B : Over S}
    [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    (U : Over S) (t : U ⟶ Over.mk (𝟙 S)) (x : U ⟶ A) :
    x ∈ (nativeMorphismKernel f).points U t ↔ x ≫ f = 1 := Iff.rfl

attribute [local instance] Picard.PoincareBundle.Kernel.Scheme.kernelGroup

theorem nativeMorphismKernel_scheme_image {S : Scheme.{u}} {A B : Over S}
    [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] :
    nativeMorphismKernel f = RelativeAnnihilator.Construction.nativeImageRelativeSubgroup (Picard.PoincareBundle.Kernel.Scheme.kernelInclusion f) := by
  ext U t x
  constructor
  · intro hx
    let z := (Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv f U).symm ⟨x, hx⟩
    exact ⟨z, congrArg Subtype.val ((Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv f U).apply_symm_apply ⟨x, hx⟩)⟩
  · rintro ⟨z, rfl⟩
    exact ((Picard.PoincareBundle.Kernel.Scheme.kernelPointsEquiv f U) z).property

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Intrinsic.MorphismKernel.Construction
