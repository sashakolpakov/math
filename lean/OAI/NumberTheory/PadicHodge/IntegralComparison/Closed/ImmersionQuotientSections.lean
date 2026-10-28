import OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.ChartSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveResolution.DualPurity
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ClosedImmersionModuleEpi

/-! # Immersion Quotient Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.ImmersionQuotientSections

noncomputable section

/-! The section module of the actual direct image of the structure
sheaf of a closed immersion is the quotient by its actual kernel ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped Pointwise

set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
  (U : Y.Opens) (hU : IsAffineOpen U)

abbrev directImage := (Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)

def sectionMap : ModuleCat.of Γ(Y, U) Γ(Y, U) ⟶
    (Affine.ModuleExactSections.sections U).obj (directImage f) :=
  (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val.app (op U)

include hU in
theorem sectionMap_surjective : Function.Surjective (sectionMap f U) :=
  f.app_surjective U hU

def quotientIso :
    ModuleCat.of Γ(Y, U) (Γ(Y, U) ⧸ RingHom.ker (f.app U).hom) ≅
      (Affine.ModuleExactSections.sections U).obj (directImage f) :=
  ((sectionMap f U).hom.quotKerEquivOfSurjective (sectionMap_surjective f U hU)).toModuleIso

def listQuotientIso (rs : List Γ(Y, U)) (hrs : RingHom.ker (f.app U).hom = Ideal.ofList rs) :
    ProjectiveResolution.DualPurity.quotient Γ(Y, U) rs ≅
      (Affine.ModuleExactSections.sections U).obj (directImage f) := by
  have heq : Ideal.ofList rs • (⊤ : Submodule Γ(Y, U) Γ(Y, U)) = RingHom.ker (f.app U).hom := by
    change Ideal.ofList rs * ⊤ = RingHom.ker (f.app U).hom
    rw [Ideal.mul_top, hrs]
  exact (Submodule.quotEquivOfEq _ _ heq).toModuleIso ≪≫ quotientIso f U hU

def chartQuotientIso (rs : List Γ(Y, U)) (hrs : RingHom.ker (f.app U).hom = Ideal.ofList rs) :
    (AffineOpen.InternalHom.sections U hU).obj (directImage f) ≅
      ProjectiveResolution.DualPurity.quotient Γ(Y, U) rs :=
  (Affine.ChartSections.iso U hU (directImage f)).symm ≪≫ (listQuotientIso f U hU rs hrs).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.ImmersionQuotientSections
