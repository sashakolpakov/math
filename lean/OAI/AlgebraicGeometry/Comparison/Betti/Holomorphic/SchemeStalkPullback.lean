import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ModulePushforwardSquare
import OAI.AlgebraicGeometry.Comparison.Betti.Analytification.RingedStalk

/-! # Scheme Stalk Pullback -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SchemeStalkPullback

noncomputable section

/-! The original algebraic and holomorphic ring stalk pullbacks form the actual analytification square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] (f : X ⟶ Y) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)

def analyticHolomorphicStalkPullback :
    ConcreteHolomorphicStalkMap.analyticHolomorphicStalk Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) →+* ConcreteHolomorphicStalkMap.analyticHolomorphicStalk X p :=
  Module.RingedStalkPushforward.Local.ringedStalkMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f) (ModulePushforwardSquare.analyticHolomorphicStructurePullback f).hom p

def algebraicSchemeStalkPullback :
    Analytification.RingedStalk.algebraicRingCatStalk Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) →+* Analytification.RingedStalk.algebraicRingCatStalk X p :=
  Module.RingedStalkPushforward.Local.ringedStalkMap f.left.base f.left.toRingCatSheafHom.hom (Analytification.Base.analytificationMap X p)

theorem analytificationRingedStalkSquare :
    (analyticHolomorphicStalkPullback f p).comp
      (Analytification.RingedStalk.analytificationRingedStalkMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p)) =
    (Analytification.RingedStalk.analytificationRingedStalkMap X p).comp (algebraicSchemeStalkPullback f p) := by
  apply RingHom.ext
  intro a
  change analyticHolomorphicStalkPullback f p
      (Analytification.RingedStalk.analytificationRingedStalkMap Y (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) a) =
    Analytification.RingedStalk.analytificationRingedStalkMap X p (algebraicSchemeStalkPullback f p a)
  obtain ⟨U, hpU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (C := RingCat) (X := TopCat.of Y.left)
    Y.left.ringCatSheaf.obj a
  dsimp only [analyticHolomorphicStalkPullback,
    algebraicSchemeStalkPullback, Analytification.RingedStalk.analytificationRingedStalkMap]
  erw [Module.RingedStalkPushforward.Local.ringedStalkMap_germ, Module.RingedStalkPushforward.Local.ringedStalkMap_germ, Module.RingedStalkPushforward.Local.ringedStalkMap_germ, Module.RingedStalkPushforward.Local.ringedStalkMap_germ]
  have hs := ConcreteCategory.congr_hom
    (NatTrans.congr_app (ModulePushforwardSquare.holomorphicRingedSquare_normalization f) (op U)) s
  exact congrArg (TopCat.Presheaf.germ (C := RingCat) (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (StructureMorphism.analyticHolomorphicStructureSheaf X).obj (Open.AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ U)) p hpU) hs.symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SchemeStalkPullback
