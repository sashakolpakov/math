import OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.Stalk
import OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.PointRange
import OAI.AlgebraicGeometry.Comparison.Betti.Closed.ModulePushforwardZero

/-! # Outside -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.Outside

noncomputable section

/-! The source and target of the actual comparison both vanish on stalks outside a closed immersion's image. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace ModuleLocal

theorem extendScalars_isZero {A S : Type} [CommRing A] [CommRing S]
    (a : A →+* S) (M : ModuleCat.{0} A) (hM : IsZero M) :
    IsZero ((ModuleCat.extendScalars a).obj M) := by
  have : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp hM
  apply ModuleCat.isZero_iff_subsingleton.mpr
  change Subsingleton (TensorProduct A ((ModuleCat.restrictScalars a).obj (ModuleCat.of S S)) M)
  infer_instance

end ModuleLocal

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y) [IsClosedImmersion f.left]

theorem moduleAnalytificationPushforwardComparison_stalk_isIso_outside
    (q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) (hq : q ∉ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f))
    (M : X.left.Modules) :
    IsIso ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
      (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf Y) q).map
        ((Analytification.Pushforward.moduleAnalytificationPushforwardComparison f).app M)) := by
  have hqZ : Analytification.Base.analytificationMap Y q ∉ Set.range f.left :=
    fun h => hq ((PointRange.closedImmersion_point_mem_range_iff f q).mpr h)
  have hA := Closed.ModulePushforwardZero.Local.closedModulePushforwardStalkZero f.left.base f.left.toRingCatSheafHom
    f.left.isClosedEmbedding.isClosed_range M (Analytification.Base.analytificationMap Y q) hqZ
  have hS := ModuleLocal.extendScalars_isZero (Analytification.RingedStalk.analytificationRingedStalkMap Y q)
    ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of Y.left) Y.left.ringCatSheaf
      (Analytification.Base.analytificationMap Y q)).obj ((Scheme.Modules.pushforward f.left).obj M)) hA
  have hsource := hS.of_iso ((Analytification.ModuleStalk.analytificationModuleStalkIso Y q).app
    ((Scheme.Modules.pushforward f.left).obj M))
  have htarget := Closed.ModulePushforwardZero.Local.closedModulePushforwardStalkZero (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
    (Holomorphic.ModulePushforwardSquare.analyticHolomorphicStructurePullback f)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion f).isClosed_range
    ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X).obj M) q hq
  exact hsource.isIso htarget _

end

end OAI.AlgebraicGeometry.Comparison.Betti.ClosedImmersion.Outside
