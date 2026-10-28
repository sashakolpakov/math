import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionRestrict
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

/-! # Structure Pullback -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.StructurePullback

noncomputable section

/-! The canonical pullback of a structure-sheaf section is ordinary
pullback of its regular function. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles

universe u

namespace Construction.StructurePullbackValues

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

theorem apply (U : X.Opens) (r : Γ(X, U)) :
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom.app (f ⁻¹ᵁ U)
      (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U r) = f.app U r := by
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  have he : ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _)
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom =
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [Adjunction.homEquiv_unit] at he
  exact congrArg (fun a : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶
    (Scheme.Modules.pushforward f).obj (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) => a.app U r) he

end Construction.StructurePullbackValues

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.StructurePullback
