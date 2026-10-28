import OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.Outside
import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.ModuleStalkIsoCriterion

/-! # Module -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.Module

noncomputable section

/-! Analytification commutes with closed-immersion pushforward through the original natural comparison for every sheaf of modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y) [IsClosedImmersion f.left]

theorem moduleAnalytificationPushforwardComparison_app_isIso (M : X.left.Modules) :
    IsIso ((Analytification.Pushforward.moduleAnalytificationPushforwardComparison f).app M) := by
  apply Sheaf.ModuleStalkIsoCriterion.Local.sheafModule_isIso_of_stalk_isIso (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
    (R := Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf Y) ((Analytification.Pushforward.moduleAnalytificationPushforwardComparison f).app M)
  intro q
  by_cases hq : q ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)
  · obtain ⟨p, rfl⟩ := hq
    exact Stalk.moduleAnalytificationPushforwardComparison_stalk_isIso f p M
  · exact Outside.moduleAnalytificationPushforwardComparison_stalk_isIso_outside f q hq M

theorem moduleAnalytificationPushforwardComparison_isIso :
    IsIso (Analytification.Pushforward.moduleAnalytificationPushforwardComparison f) := by
  have (M : X.left.Modules) : IsIso ((Analytification.Pushforward.moduleAnalytificationPushforwardComparison f).app M) :=
    moduleAnalytificationPushforwardComparison_app_isIso f M
  exact NatIso.isIso_of_isIso_app (Analytification.Pushforward.moduleAnalytificationPushforwardComparison f)

def moduleAnalytificationClosedPushforwardIso :
    Scheme.Modules.pushforward f.left ⋙ Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification Y ≅
      Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X ⋙ Holomorphic.ModulePushforwardSquare.analyticHolomorphicModulePushforward f := by
  have := moduleAnalytificationPushforwardComparison_isIso f
  exact asIso (Analytification.Pushforward.moduleAnalytificationPushforwardComparison f)

theorem moduleAnalytificationClosedPushforwardIso_hom :
    (moduleAnalytificationClosedPushforwardIso f).hom =
      Analytification.Pushforward.moduleAnalytificationPushforwardComparison f := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.Module
