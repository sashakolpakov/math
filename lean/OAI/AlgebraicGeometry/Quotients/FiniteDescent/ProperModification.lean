import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BirationalStructure
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BirationalGeneric

/-! # Proper Modification -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperModification.Construction.ProperModificationFunctions

noncomputable section

/-! Proper modifications of a normal integral scheme preserve its structure sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
variable (f : X ⟶ Y) [IsProper f]
variable (U : Y.Opens) [Nonempty U] [IsIso (f ∣_ U)]

include hY U

theorem isIso_app (V : Y.Opens) : IsIso (f.app V) := by
  have := BirationalGeneric.Construction.BirationalGenericLift.isDominant_lift f U
  exact BirationalStructure.Construction.BirationalStructureSheaf.isIso_app hY f (BirationalGeneric.Construction.BirationalGenericLift.lift f U)
    (BirationalGeneric.Construction.BirationalGenericLift.lift_comp f U) V

theorem isIso_unit : IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  have := BirationalGeneric.Construction.BirationalGenericLift.isDominant_lift f U
  exact BirationalStructure.Construction.BirationalStructureSheaf.isIso_unit hY f (BirationalGeneric.Construction.BirationalGenericLift.lift f U)
    (BirationalGeneric.Construction.BirationalGenericLift.lift_comp f U)

def iso : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ≅ (Scheme.Modules.pushforward f).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :=
  @asIso _ _ _ _ (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
    (isIso_unit hY f U)

omit hY in
theorem smooth_isIso_app {K : Type u} [Field K] [IsAlgClosed K]
    (p : Y ⟶ Spec (.of K)) [Smooth p] (V : Y.Opens) : IsIso (f.app V) := by
  apply isIso_app _ f U V
  intro y
  have := SmoothStalk.Construction.SmoothStalkFactorial.stalk p y
  infer_instance

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProperModification.Construction.ProperModificationFunctions
