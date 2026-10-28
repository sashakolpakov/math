import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.ExtensionCoordinates

/-! # Coface Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.CofaceCoordinates

noncomputable section

/-! Actual algebraic Cech coface maps have the original open
restriction formula in their regular-function coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open _root_.TopCat.Sheaf

variable {X : Scheme.{0}} {I : Type} (U : I → X.Opens)

theorem cechCoefficient_coface (n : ℕ) (k : Fin (n + 2)) (W : X.Opens)
    (a : Γ(TermModules.cechTermModule X U n, W)) (i : Fin (n + 2) → I) :
    ExtensionCoordinates.cechCoefficient U (n + 1) W ((ModuleDifferential.cechModuleCoface X U n k).app W a) i =
      X.presheaf.map (homOfLE (inf_le_inf_left W (ExtensionCoordinates.cechIntersection_le_face U n k i))).op
        (ExtensionCoordinates.cechCoefficient U n W a (ExtensionCoordinates.cechFaceIndex n k i)) := by
  have he := congrArg (fun f => f.hom.app (op W) a) (ModuleDifferential.cechModuleCoface_underlying X U n k)
  exact (congrArg (fun b => ExtensionCoordinates.cechCoefficient U (n + 1) W b i) he).trans
    (SheafCohomology.Cech.SheafDifferential.TopCat.Sheaf.cechCoface_apply (TermModules.structureAbelianSheaf X) U n W a k i)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Cech.CofaceCoordinates
