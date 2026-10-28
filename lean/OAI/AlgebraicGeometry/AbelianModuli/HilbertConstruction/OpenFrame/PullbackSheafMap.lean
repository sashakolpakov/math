import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackCompatibility
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.ModuleSheaf

/-! # Pullback Sheaf Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackSheafMap

noncomputable section

/-! The explicit pullback of frame coefficients induces an actual sheaf morphism and its adjoint comparison from the canonical pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {ι : Type u} {U : ι → Y.Opens} (D : Transitions.OpenFrameTransitions U) (f : X ⟶ Y)

local instance (W : Y.Opensᵒᵖ) : Module Γ(Y, W.unop) ((ModuleSheaf.openFrameModuleSheaf D).val.obj W) :=
  ((ModuleSheaf.openFrameModuleSheaf D).val.obj W).isModule

local instance (W : Y.Opensᵒᵖ) : Module Γ(Y, W.unop)
    (((Scheme.Modules.pushforward f).obj (ModuleSheaf.openFrameModuleSheaf (D.pullback f))).val.obj W) :=
  (((Scheme.Modules.pushforward f).obj (ModuleSheaf.openFrameModuleSheaf (D.pullback f))).val.obj W).isModule

def openFramePullbackAdjoint :
    ModuleSheaf.openFrameModuleSheaf D ⟶ (Scheme.Modules.pushforward f).obj (ModuleSheaf.openFrameModuleSheaf (D.pullback f)) where
  val.app W := ModuleCat.ofHom (X := (ModuleSheaf.openFrameModuleSheaf D).val.obj W)
    (Y := ((Scheme.Modules.pushforward f).obj (ModuleSheaf.openFrameModuleSheaf (D.pullback f))).val.obj W) {
    toFun := PullbackCompatibility.openFrameSectionPullback D f W.unop
    map_add' := (PullbackCompatibility.openFrameSectionPullback D f W.unop).map_add
    map_smul' := (PullbackCompatibility.openFrameSectionPullback D f W.unop).map_smulₛₗ }
  val.naturality {V W} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact PullbackTuples.openFramePullbackTuple_restrict U f h.unop.le x.val

def openFramePullbackComparison :
    (Scheme.Modules.pullback f).obj (ModuleSheaf.openFrameModuleSheaf D) ⟶ ModuleSheaf.openFrameModuleSheaf (D.pullback f) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm (openFramePullbackAdjoint D f)

theorem openFramePullbackComparison_adjoint :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (openFramePullbackComparison D f) =
      openFramePullbackAdjoint D f :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).apply_symm_apply _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.PullbackSheafMap
