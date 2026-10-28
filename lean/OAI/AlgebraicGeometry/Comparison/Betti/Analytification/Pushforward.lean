import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ModulePushforwardSquare

/-! # Pushforward -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytification.Pushforward

noncomputable section

section

/-! The natural comparison from analytification after algebraic pushforward to holomorphic pushforward. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y)

def moduleAnalytificationPushforwardUnit :
    Scheme.Modules.pushforward f.left ⟶
      (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X ⋙ Holomorphic.ModulePushforwardSquare.analyticHolomorphicModulePushforward f) ⋙
        Holomorphic.StructureMorphism.holomorphicModuleDirectImage Y :=
  (Functor.leftUnitor (Scheme.Modules.pushforward f.left)).inv ≫
    Functor.whiskerRight (Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction X).unit
      (Scheme.Modules.pushforward f.left) ≫
    (Functor.associator (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X)
      (Holomorphic.StructureMorphism.holomorphicModuleDirectImage X) (Scheme.Modules.pushforward f.left)).hom ≫
    Functor.whiskerLeft (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X)
      (Holomorphic.ModulePushforwardSquare.holomorphicModulePushforwardSquareIso f).hom ≫
    (Functor.associator (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X)
      (Holomorphic.ModulePushforwardSquare.analyticHolomorphicModulePushforward f) (Holomorphic.StructureMorphism.holomorphicModuleDirectImage Y)).inv

def moduleAnalytificationPushforwardComparison :
    Scheme.Modules.pushforward f.left ⋙ Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification Y ⟶
      Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X ⋙ Holomorphic.ModulePushforwardSquare.analyticHolomorphicModulePushforward f where
  app M := ((Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction Y).homEquiv _ _).symm
    ((moduleAnalytificationPushforwardUnit f).app M)
  naturality {M N} g :=
    (Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction Y).homEquiv_naturality_right_square
      ((Scheme.Modules.pushforward f.left).map g)
      ((moduleAnalytificationPushforwardUnit f).app N)
      ((moduleAnalytificationPushforwardUnit f).app M)
      ((Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X ⋙ Holomorphic.ModulePushforwardSquare.analyticHolomorphicModulePushforward f).map g)
      ((moduleAnalytificationPushforwardUnit f).naturality g)

theorem moduleAnalytificationPushforwardComparison_unit (M : X.left.Modules) :
    (Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction Y).unit.app ((Scheme.Modules.pushforward f.left).obj M) ≫
      (Holomorphic.StructureMorphism.holomorphicModuleDirectImage Y).map ((moduleAnalytificationPushforwardComparison f).app M) =
        (moduleAnalytificationPushforwardUnit f).app M := by
  exact ((Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction Y).homEquiv _ _).apply_symm_apply _

end

/-! The pushforward comparison uses the original analytification unit on every actual section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y)

theorem holomorphicModulePushforwardSquareIso_sections
    (M : SheafOfModules.{0} (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X))
    (U : Y.left.Opens) (m : M.val.obj (op (Open.AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ U)))) :
    (((Holomorphic.ModulePushforwardSquare.holomorphicModulePushforwardSquareIso f).hom.app M).val.app (op U)) m = m := rfl

theorem moduleAnalytificationPushforwardUnit_sections
    (M : X.left.Modules) (U : Y.left.Opens) (m : M.val.obj (op (f.left ⁻¹ᵁ U))) :
    (((moduleAnalytificationPushforwardUnit f).app M).val.app (op U)) m =
      (((Holomorphic.StructureMorphism.holomorphicModuleAnalytificationAdjunction X).unit.app M).val.app
        (op (f.left ⁻¹ᵁ U))) m := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytification.Pushforward
