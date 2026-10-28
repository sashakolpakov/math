import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleSections
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.StructurePullback

/-! # Structure Sections -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.StructureSections

noncomputable section

/-! On the structure sheaf, the base-linear module pullback restricted to
a smaller open is exactly the usual pullback of regular functions. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.StructureSectionsOver

variable {X Y S : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ S)
variable (h : f ≫ π = ρ)

theorem apply (U : X.Opens) (V : Y.Opens) (hVU : V ≤ f ⁻¹ᵁ U) (s : Γ(X, U)) :
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom.app V
      (ModuleSections.Construction.ModuleSectionsOver.map f π ρ h (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U V hVU s) =
        f.appLE U V hVU s := by
  rw [ModuleSections.Construction.ModuleSectionsOver.map_apply]
  have he := PresheafOfModules.naturality_apply (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom.val
    (homOfLE hVU).op (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U s)
  change (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom.app V
      (((Scheme.Modules.pullback f).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).presheaf.map
        (homOfLE hVU).op (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U s)) =
    Y.presheaf.map (homOfLE hVU).op
      ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom.app (f ⁻¹ᵁ U)
        (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U s)) at he
  rw [he, StructurePullback.Construction.StructurePullbackValues.apply]
  rfl

end Construction.StructureSectionsOver

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.StructureSections
