import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPullbackComposition
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionRestrict

/-! # Pullback Section Composition -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionComposition

noncomputable section

/-! The canonical maps on module sections respect successive pullbacks. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.PullbackSectionCoefficients

variable {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) (M : X.Modules)

theorem comp_inv (U : X.Opens) (s : Γ(M, U)) :
    PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map g ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U) (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U s) =
      ((Scheme.Modules.pullbackComp g f).inv.app M).app ((g ≫ f) ⁻¹ᵁ U)
        (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map (g ≫ f) M U s) :=
  congrArg (fun a : M ⟶ (Scheme.Modules.pushforward (g ≫ f)).obj
      ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback f).obj M)) => a.app U s)
    (TensorPullbackComposition.Construction.TensorPullbackMap.pullbackComp_unit g f M)

theorem comp (U : X.Opens) (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp g f).hom.app M).app ((g ≫ f) ⁻¹ᵁ U)
      (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map g ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U) (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U s)) =
        PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map (g ≫ f) M U s := by
  rw [comp_inv]
  exact congrArg (fun a : (Scheme.Modules.pullback (g ≫ f)).obj M ⟶
      (Scheme.Modules.pullback (g ≫ f)).obj M => a.app ((g ≫ f) ⁻¹ᵁ U) (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map (g ≫ f) M U s))
    ((Scheme.Modules.pullbackComp g f).app M).inv_hom_id

end Construction.PullbackSectionCoefficients

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionComposition
