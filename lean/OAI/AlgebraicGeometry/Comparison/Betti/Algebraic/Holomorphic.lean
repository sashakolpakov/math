import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.HolomorphicForms
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Factorization

/-! # Holomorphic -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Holomorphic

noncomputable section

/-! The preserved global and open algebraic maps factor through actual holomorphic differential forms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

attribute [local instance] Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def globalHolomorphicCochainMap :
    Forms.algebraicDeRhamComplex Γ(X.left, ⊤) ⟶
      Holomorphic.DeRhamComplex.complex (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
  Holomorphic.Factorization.Smooth.holomorphicCochainMap (RegularFunctions.globalSectionContinuousAlgHom X)
    (fun s => RegularSmoothness.globalEvaluation_real_contMDiff X s ∞)
    (fun s => RegularSmoothness.globalEvaluation_contMDiff X s ∞)

theorem globalHolomorphicCochainMap_factorization :
    globalHolomorphicCochainMap X ≫
        Holomorphic.DeRhamComplex.inclusionCochainMap (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) =
      GlobalSmoothCochain.globalSmoothCochainMap X :=
  Holomorphic.Factorization.Smooth.holomorphicCochainMap_factorization (RegularFunctions.globalSectionContinuousAlgHom X)
    (fun s => RegularSmoothness.globalEvaluation_real_contMDiff X s ∞)
    (fun s => RegularSmoothness.globalEvaluation_contMDiff X s ∞)

def openHolomorphicCochainMap (U : X.left.Opens) :
    Forms.algebraicDeRhamComplex Γ(X.left, U) ⟶
      Holomorphic.DeRhamComplex.complex (RegularSmoothness.NativeModel X) (Open.AffineIsoEvaluation.analyticOpen X U) :=
  Holomorphic.Factorization.Smooth.holomorphicCochainMap (Open.AffineIsoEvaluation.sectionEvaluationOn X U) (Open.SmoothEvaluation.sectionEvaluationOn_smooth X U)
    (HodgeConjecture.CMExtraction.HolomorphicSections.Kaehler.sectionEvaluationOn_holomorphic X U)

theorem openHolomorphicCochainMap_factorization (U : X.left.Opens) :
    (openHolomorphicCochainMap X U ≫
        Holomorphic.DeRhamComplex.inclusionCochainMap (RegularSmoothness.NativeModel X) (Open.AffineIsoEvaluation.analyticOpen X U)) ≫
        (Analysis.DifferentialForms.Manifold.IntrinsicOpenDeRham.intrinsicOpenDeRhamIso (RegularSmoothness.NativeModel X) (Open.AffineIsoEvaluation.analyticOpen X U)).inv =
      Open.SmoothForms.openSmoothCochainMap X U := by
  change (Holomorphic.Factorization.Smooth.holomorphicCochainMap (Open.AffineIsoEvaluation.sectionEvaluationOn X U) (Open.SmoothEvaluation.sectionEvaluationOn_smooth X U)
      (HodgeConjecture.CMExtraction.HolomorphicSections.Kaehler.sectionEvaluationOn_holomorphic X U) ≫ _) ≫ _ = _
  rw [Holomorphic.Factorization.Smooth.holomorphicCochainMap_factorization]
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.Holomorphic
