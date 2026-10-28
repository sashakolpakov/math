import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalKernelLinearization
import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition

/-! # Action Laws -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActionLaws.Construction

noncomputable section

/-! Name the actual unit and cocycle equations separately before
assembling their kernel-action linearization. -/

open _root_.CategoryTheory Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u v u' v'

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.ActionMaps OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalKernelLinearization
open Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [Limits.HasPullbacks C]
variable {V W : C} [GrpObj V] [GrpObj W] (p : V ⟶ W) [IsMonHom p]
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}) (L : F.obj (.mk (op V)))
variable (e : (F.map (Picard.PoincareBundle.Kernel.ActionMaps.source p).op.toLoc).toFunctor.obj L ≅ (F.map (Picard.PoincareBundle.Kernel.ActionMaps.action p).op.toLoc).toFunctor.obj L)

def KernelActionUnit : Prop :=
  pullHom e.hom (Picard.PoincareBundle.Kernel.ActionMaps.unitSection p) (𝟙 V) (𝟙 V) (Picard.PoincareBundle.Kernel.ActionMaps.unitSection_source p) (Picard.PoincareBundle.Kernel.ActionMaps.unitSection_action p) = 𝟙 _

def KernelActionCocycle : Prop :=
  pullHom e.hom (Picard.PoincareBundle.Kernel.ActionMaps.firstStep p) (Picard.PoincareBundle.Kernel.ActionMaps.tripleSource p) (Picard.PoincareBundle.Kernel.ActionMaps.tripleMiddle p) rfl rfl ≫
    pullHom e.hom (Picard.PoincareBundle.Kernel.ActionMaps.secondStep p) (Picard.PoincareBundle.Kernel.ActionMaps.tripleMiddle p) (Picard.PoincareBundle.Kernel.ActionMaps.tripleTarget p) (Picard.PoincareBundle.Kernel.ActionMaps.secondStep_source p) rfl =
    pullHom e.hom (Picard.PoincareBundle.Kernel.ActionMaps.productStep p) (Picard.PoincareBundle.Kernel.ActionMaps.tripleSource p) (Picard.PoincareBundle.Kernel.ActionMaps.tripleTarget p) (Picard.PoincareBundle.Kernel.ActionMaps.productStep_source p) (Picard.PoincareBundle.Kernel.ActionMaps.productStep_action p)

theorem kernelActionCocycle_of_pullIso
    (e₁ : (F.map (Picard.PoincareBundle.Kernel.ActionMaps.tripleSource p).op.toLoc).toFunctor.obj L ≅ (F.map (Picard.PoincareBundle.Kernel.ActionMaps.tripleMiddle p).op.toLoc).toFunctor.obj L)
    (e₂ : (F.map (Picard.PoincareBundle.Kernel.ActionMaps.tripleMiddle p).op.toLoc).toFunctor.obj L ≅ (F.map (Picard.PoincareBundle.Kernel.ActionMaps.tripleTarget p).op.toLoc).toFunctor.obj L)
    (e₃ : (F.map (Picard.PoincareBundle.Kernel.ActionMaps.tripleSource p).op.toLoc).toFunctor.obj L ≅ (F.map (Picard.PoincareBundle.Kernel.ActionMaps.tripleTarget p).op.toLoc).toFunctor.obj L)
    (h₁ : Picard.PoincareBundle.PullbackFiberComposition.pullIso F e (Picard.PoincareBundle.Kernel.ActionMaps.firstStep p) (Picard.PoincareBundle.Kernel.ActionMaps.tripleSource p) (Picard.PoincareBundle.Kernel.ActionMaps.tripleMiddle p) rfl rfl = e₁)
    (h₂ : Picard.PoincareBundle.PullbackFiberComposition.pullIso F e (Picard.PoincareBundle.Kernel.ActionMaps.secondStep p) (Picard.PoincareBundle.Kernel.ActionMaps.tripleMiddle p) (Picard.PoincareBundle.Kernel.ActionMaps.tripleTarget p)
      (Picard.PoincareBundle.Kernel.ActionMaps.secondStep_source p) rfl = e₂)
    (h₃ : Picard.PoincareBundle.PullbackFiberComposition.pullIso F e (Picard.PoincareBundle.Kernel.ActionMaps.productStep p) (Picard.PoincareBundle.Kernel.ActionMaps.tripleSource p) (Picard.PoincareBundle.Kernel.ActionMaps.tripleTarget p)
      (Picard.PoincareBundle.Kernel.ActionMaps.productStep_source p) (Picard.PoincareBundle.Kernel.ActionMaps.productStep_action p) = e₃)
    (hc : e₁ ≪≫ e₂ = e₃) : KernelActionCocycle p F L e :=
  (congrArg₂ (fun a b => a ≫ b) (congrArg Iso.hom h₁) (congrArg Iso.hom h₂)).trans
    ((congrArg Iso.hom hc).trans (congrArg Iso.hom h₃).symm)

def kernelActionLinearization (hu : KernelActionUnit p F L e) (hc : KernelActionCocycle p F L e) :
    Picard.PoincareBundle.GlobalKernelLinearization.ActionLinearization p F L := ⟨e, hu, hc⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ActionLaws.Construction
