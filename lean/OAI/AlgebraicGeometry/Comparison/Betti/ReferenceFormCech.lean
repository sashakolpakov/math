import OAI.AlgebraicGeometry.Comparison.Betti.Cech.PullbackNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Module.AnalytificationCechMap
import OAI.AlgebraicGeometry.Comparison.Betti.Analytification.Term
import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ExteriorAcyclicity

/-! # Reference Form Cech -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ReferenceFormCech

noncomputable section

/-! The original algebraic-to-holomorphic form map is the normalized module comparison on each Čech column. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Comparison.Betti.Cech.PullbackNaturality

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def analyticHolomorphicFormAdditiveSheaf (r : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) :=
  (sheafCompose (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj ((Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex X).X r)

def originalHolomorphicFormAdditiveMap (r : ℕ) :
    (Affine.ExteriorAcyclicity.algebraicFormAdditiveSheaf X r).obj ⟶ (Opens.map (Analytification.Base.analytificationMap X)).op ⋙
      (analyticHolomorphicFormAdditiveSheaf X r).obj :=
  ((sheafCompose (Opens.grothendieckTopology X.left)
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).map ((Algebraic.HolomorphicSheafMap.algebraicToHolomorphicSheafMap X).f r)).hom

variable {ι : Type} (U : ι → X.left.Opens)

def algebraicHolomorphicFormCechMap (r : ℕ) :
    (cechComplexFunctor U).obj (Affine.ExteriorAcyclicity.algebraicFormAdditiveSheaf X r).obj ⟶
      (cechComplexFunctor (fun i => Open.AffineIsoEvaluation.analyticOpen X (U i))).obj
        (analyticHolomorphicFormAdditiveSheaf X r).obj :=
  Cech.PullbackGlobalIsomorphism.additiveCechPullbackMap (Analytification.Base.analytificationMap X) U (Affine.ExteriorAcyclicity.algebraicFormAdditiveSheaf X r)
    (analyticHolomorphicFormAdditiveSheaf X r) (originalHolomorphicFormAdditiveMap X r)

theorem algebraicHolomorphicFormCechMap_normalization (r : ℕ) :
    (cechComplexFunctor U).map (Exterior.ModuleForget.exteriorFormsModuleSheafForgetIso X r).hom.hom ≫
        algebraicHolomorphicFormCechMap X U r =
      Module.AnalytificationCechMap.moduleAnalytificationCechMap X (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X r) U ≫
        (cechComplexFunctor (fun i => Open.AffineIsoEvaluation.analyticOpen X (U i))).map
          (Analytification.Term.analyticExteriorFormForgetIso X r).hom.hom := by
  have h : (Exterior.ModuleForget.exteriorFormsModuleSheafForgetIso X r).hom.hom ≫
      originalHolomorphicFormAdditiveMap X r =
    Module.AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit X (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X r) ≫
      Functor.whiskerLeft (Opens.map (Analytification.Base.analytificationMap X)).op (Analytification.Term.analyticExteriorFormForgetIso X r).hom.hom :=
    congrArg (fun g => g.hom) (Analytification.Term.algebraicToHolomorphicSheafMap_eq_analytificationUnit X r)
  exact Cech.PullbackNaturality.additiveCechPullbackMap_square (Analytification.Base.analytificationMap X) U
    (Exterior.ModuleForget.exteriorFormsModuleSheafForgetIso X r).hom (Analytification.Term.analyticExteriorFormForgetIso X r).hom
    (Module.AnalytificationAdditiveUnit.moduleAnalytificationAdditiveUnit X (Exterior.ModuleSheaf.exteriorFormsModuleSheaf X r))
    (originalHolomorphicFormAdditiveMap X r) h

end

end OAI.AlgebraicGeometry.Comparison.Betti.ReferenceFormCech
