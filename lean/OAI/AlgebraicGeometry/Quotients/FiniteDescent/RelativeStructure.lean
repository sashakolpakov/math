import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RelativeFunctionsIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.LineRigidificationAt

/-! # Relative Structure -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.RelativeStructure.Construction.RelativeStructureSheaf

noncomputable section

/-! The structure sheaf and uniqueness of line-bundle isomorphisms under relative rigidity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f]
variable [GeometricallyConnected f] [IsReduced X]
variable (e : S ⟶ X) (he : e ≫ f = 𝟙 S)

include he

/-- Pullback of functions identifies the structure sheaf of the base with
the pushforward of the structure sheaf of the source. -/
theorem isIso_unit : IsIso (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
  apply (Scheme.Modules.Hom.isIso_iff_isIso_app).mpr
  intro V
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have hi := RelativeFunctionsIs.Construction.RelativeFunctions.isIso_app f e he V
  exact (ConcreteCategory.isIso_iff_bijective (f.app V)).mp hi

def iso : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S ≅ (Scheme.Modules.pushforward f).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) :=
  @asIso _ _ _ _ (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
    (isIso_unit f e he)

/-- An existing global isomorphism can be uniquely normalized to any prescribed
isomorphism along the section. This establishes uniqueness, not existence of
an isomorphism from fiberwise information. -/
theorem existsUnique_iso (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (a : L.sheaf ≅ M.sheaf)
    (φ : (L.pullback e).sheaf ≅ (M.pullback e).sheaf) :
    ∃! b : L.sheaf ≅ M.sheaf, (Scheme.Modules.pullback e).mapIso b = φ := by
  have : IsIso e.appTop := (RelativeFunctionsIs.Construction.RelativeFunctions.iso f e he).isIso_inv
  exact LineRigidificationAt.Construction.LineRigidification.existsUnique_iso e L M a φ

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.RelativeStructure.Construction.RelativeStructureSheaf
