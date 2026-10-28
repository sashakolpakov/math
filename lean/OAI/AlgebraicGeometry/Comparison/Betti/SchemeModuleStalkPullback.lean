import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SchemeStalkPullback
import OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.ModulePushforwardStalk
import OAI.AlgebraicGeometry.Comparison.Betti.SeparatedPointTopology

/-! # Scheme Module Stalk Pullback -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SchemeModuleStalkPullback

noncomputable section

/-! The actual algebraic and holomorphic module pushforward stalk maps, with section formulas and bijectivity for closed immersions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.AlgebraicGeometry.Comparison.Betti.Sheaf.ModulePushforwardStalk.Local

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)

def algebraicModulePushforwardStalkHom (M : X.left.Modules) :
    (StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of Y.left) Y.left.ringCatSheaf
      (Analytification.Base.analytificationMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p))).obj
        ((Scheme.Modules.pushforward f.left).obj M) ⟶
      (ModuleCat.restrictScalars (Holomorphic.SchemeStalkPullback.algebraicSchemeStalkPullback f p)).obj
        ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of X.left) X.left.ringCatSheaf
          (Analytification.Base.analytificationMap X p)).obj M) :=
  Module.RingedStalkPushforward.Local.modulePushforwardStalkHom f.left.base f.left.toRingCatSheafHom.hom
    (Analytification.Base.analytificationMap X p) M.val

def holomorphicModulePushforwardStalkHom
    (M : SheafOfModules.{0} (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X)) :
    (StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
      (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf Y) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)).obj
        ((Holomorphic.ModulePushforwardSquare.analyticHolomorphicModulePushforward f).obj M) ⟶
      (ModuleCat.restrictScalars (Holomorphic.SchemeStalkPullback.analyticHolomorphicStalkPullback f p)).obj
        ((StalkPointModuleAdjunction.Local.sheafRingModuleStalk (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
          (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X) p).obj M) :=
  Module.RingedStalkPushforward.Local.modulePushforwardStalkHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
    (Holomorphic.ModulePushforwardSquare.analyticHolomorphicStructurePullback f).hom p M.val

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom] in
theorem algebraicModulePushforwardStalkHom_germ (M : X.left.Modules)
    (U : Y.left.Opens) (hpU : Analytification.Base.analytificationMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) ∈ U)
    (m : M.val.obj (op (f.left ⁻¹ᵁ U))) :
    algebraicModulePushforwardStalkHom f p M
      (TopCat.Presheaf.germ (C := AddCommGrpCat) (X := TopCat.of Y.left)
        ((Scheme.Modules.pushforward f.left).obj M).val.presheaf U
        (Analytification.Base.analytificationMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)) hpU m) =
      TopCat.Presheaf.germ (C := AddCommGrpCat) (X := TopCat.of X.left)
        M.val.presheaf (f.left ⁻¹ᵁ U) (Analytification.Base.analytificationMap X p) hpU m :=
  Module.RingedStalkPushforward.Local.modulePushforwardAdditiveStalkMap_germ f.left.base f.left.toRingCatSheafHom.hom
    M.val (Analytification.Base.analytificationMap X p) U hpU m

theorem holomorphicModulePushforwardStalkHom_germ
    (M : SheafOfModules.{0} (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X))
    (U : TopologicalSpace.Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (hpU : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p ∈ U)
    (m : M.val.obj (op (Holomorphic.ModulePushforwardSquare.analyticSchemePreimageOpen f U))) :
    holomorphicModulePushforwardStalkHom f p M
      (TopCat.Presheaf.germ (C := AddCommGrpCat) (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
        ((Holomorphic.ModulePushforwardSquare.analyticHolomorphicModulePushforward f).obj M).val.presheaf U
        (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) hpU m) =
      TopCat.Presheaf.germ (C := AddCommGrpCat) (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        M.val.presheaf (Holomorphic.ModulePushforwardSquare.analyticSchemePreimageOpen f U) p hpU m :=
  Module.RingedStalkPushforward.Local.modulePushforwardAdditiveStalkMap_germ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
    (Holomorphic.ModulePushforwardSquare.analyticHolomorphicStructurePullback f).hom M.val p U hpU m

omit [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom] in
theorem algebraicModulePushforwardStalkHom_bijective [IsClosedImmersion f.left]
    (M : X.left.Modules) : Function.Bijective (algebraicModulePushforwardStalkHom f p M) :=
  Module.RingedStalkPushforward.Local.ringModulePushforwardStalkMap_bijective f.left.base f.left.toRingCatSheafHom.hom
    M.val (Analytification.Base.analytificationMap X p) f.left.isClosedEmbedding.isInducing

theorem holomorphicModulePushforwardStalkHom_bijective [IsClosedImmersion f.left]
    (M : SheafOfModules.{0} (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X)) :
    Function.Bijective (holomorphicModulePushforwardStalkHom f p M) :=
  Module.RingedStalkPushforward.Local.ringModulePushforwardStalkMap_bijective (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f)
    (Holomorphic.ModulePushforwardSquare.analyticHolomorphicStructurePullback f).hom M.val p
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isClosedEmbedding_map_of_isClosedImmersion f).isInducing

end

end OAI.AlgebraicGeometry.Comparison.Betti.SchemeModuleStalkPullback
