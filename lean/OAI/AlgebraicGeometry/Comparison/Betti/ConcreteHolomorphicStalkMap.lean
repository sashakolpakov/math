import OAI.AlgebraicGeometry.Comparison.Betti.ManifoldHolomorphicStalk
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StructureMorphism

/-! # Concrete Holomorphic Stalk Map -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ConcreteHolomorphicStalkMap

noncomputable section

/-! The original regular-to-holomorphic sheaf morphism induces the
actual algebraic-to-analytic local ring map. Its formula on every
regular section is retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.Comparison.Betti.ManifoldHolomorphicStalk.AnalyticLocal

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

abbrev analyticHolomorphicStalk (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) : RingCat :=
  ManifoldHolomorphicStalk.AnalyticLocal.manifoldStructureStalk (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) p

theorem analyticHolomorphicStalk_noetherian (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    IsNoetherianRing (analyticHolomorphicStalk X p) :=
  ManifoldHolomorphicStalk.AnalyticLocal.manifoldStructureStalk_noetherian (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) p

def algebraicHolomorphicStalkMap (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    X.left.presheaf.stalk (Analytification.Base.analytificationMap X p) →+* analyticHolomorphicStalk X p :=
  ((CommRingStalkForget.AnalyticLocal.commRingStalkForgetIso X.left.presheaf (Analytification.Base.analytificationMap X p)).hom ≫
    (TopCat.Presheaf.stalkFunctor (X := TopCat.of X.left) RingCat (Analytification.Base.analytificationMap X p)).map
      (Holomorphic.StructureMorphism.algebraicToHolomorphicStructureSheaf X).hom ≫
    TopCat.Presheaf.stalkPushforward RingCat (Analytification.Base.analytificationMap X)
      (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X).obj p).hom

theorem algebraicHolomorphicStalkMap_germ (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (U : X.left.Opens)
    (hp : Analytification.Base.analytificationMap X p ∈ U) (s : Γ(X.left, U)) :
    algebraicHolomorphicStalkMap X p (X.left.presheaf.germ U (Analytification.Base.analytificationMap X p) hp s) =
      TopCat.Presheaf.germ (C := RingCat) (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
        (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X).obj (Open.AffineIsoEvaluation.analyticOpen X U) p hp
          (Holomorphic.RegularSections.regularHolomorphicSectionMap X U s) := by
  have hforget : (CommRingStalkForget.AnalyticLocal.commRingStalkForgetIso X.left.presheaf (Analytification.Base.analytificationMap X p)).hom
      (X.left.presheaf.germ U (Analytification.Base.analytificationMap X p) hp s) =
        TopCat.Presheaf.germ (C := RingCat) (X := TopCat.of X.left) X.left.ringCatSheaf.obj
          U (Analytification.Base.analytificationMap X p) hp s := by
    apply (CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv X.left.presheaf (Analytification.Base.analytificationMap X p)).injective
    exact (CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv X.left.presheaf (Analytification.Base.analytificationMap X p)).apply_symm_apply
      (X.left.presheaf.germ U (Analytification.Base.analytificationMap X p) hp s) |>.trans
        (CommRingStalkForget.AnalyticLocal.commRingStalkForgetEquiv_germ X.left.presheaf (Analytification.Base.analytificationMap X p) U hp s).symm
  change TopCat.Presheaf.stalkPushforward RingCat (Analytification.Base.analytificationMap X)
    (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X).obj p
      ((TopCat.Presheaf.stalkFunctor (X := TopCat.of X.left) RingCat (Analytification.Base.analytificationMap X p)).map
        (Holomorphic.StructureMorphism.algebraicToHolomorphicStructureSheaf X).hom
          ((CommRingStalkForget.AnalyticLocal.commRingStalkForgetIso X.left.presheaf (Analytification.Base.analytificationMap X p)).hom
            (X.left.presheaf.germ U (Analytification.Base.analytificationMap X p) hp s))) = _
  rw [hforget]
  exact (congrArg (TopCat.Presheaf.stalkPushforward RingCat (Analytification.Base.analytificationMap X)
      (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X).obj p)
    (TopCat.Presheaf.stalkFunctor_map_germ_apply (X := TopCat.of X.left) U
      (Analytification.Base.analytificationMap X p) hp (Holomorphic.StructureMorphism.algebraicToHolomorphicStructureSheaf X).hom s)).trans
        (TopCat.Presheaf.stalkPushforward_germ_apply RingCat (Analytification.Base.analytificationMap X)
          (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X).obj U p hp (Holomorphic.RegularSections.regularHolomorphicSectionMap X U s))

end

end OAI.AlgebraicGeometry.Comparison.Betti.ConcreteHolomorphicStalkMap
