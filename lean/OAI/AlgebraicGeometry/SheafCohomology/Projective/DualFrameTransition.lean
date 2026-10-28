import OAI.AlgebraicGeometry.SheafCohomology.Projective.DualOverlapTransition

/-! # Dual Frame Transition -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.DualFrameTransition

noncomputable section

/-! A transition relation retaining its frames as explicit arguments. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v

def FrameTransition {C : Type u} [Category.{v} C] {A B : C}
    (e f : A ≅ B) (s : B ⟶ B) : Prop := e.hom = f.hom ≫ s

theorem dualOpenOverlap_frameTransition {X : Scheme.{u}} (M : X.Modules)
    {U V W : X.Opens} (hU : W ≤ U) (hV : W ≤ V)
    (e : M.restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme)
    (g : M.restrict V.ι ≅ Invertible.Scheme.Modules.unitObj V.toScheme)
    (a : (Dual.Scheme.Modules.dualObj M).restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme)
    (b : (Dual.Scheme.Modules.dualObj M).restrict V.ι ≅ Invertible.Scheme.Modules.unitObj V.toScheme)
    (ha : a = Dual.Scheme.Modules.dualRestrictIsoOfRestrictIso M U e)
    (hb : b = Dual.Scheme.Modules.dualRestrictIsoOfRestrictIso M V g)
    (s : Γ(X, W))
    (h : (Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M V
      (Invertible.Scheme.Modules.overTrivializationOfRestrictIso M V g)
      (Over.mk (homOfLE hV))).hom =
      (Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U
        (Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e)
        (Over.mk (homOfLE hU))).hom ≫
      Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf W s) :
    FrameTransition (OpenFrames.Scheme.Modules.restrictOpenTrivialization hU a)
      (OpenFrames.Scheme.Modules.restrictOpenTrivialization hV b)
      (UnitScalar.unitEndomorphismOfTopSection (OpenFrames.Scheme.Modules.openTopSection W s)) := by
  rw [ha, hb]
  exact DualOverlapTransition.dualOpenOverlap_transition M hU hV e g s h

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.DualFrameTransition
