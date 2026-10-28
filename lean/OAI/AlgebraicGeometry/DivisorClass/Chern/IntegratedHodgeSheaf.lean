import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.IntegrationConnecting
import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.SectionCohomologyMap
import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.HodgeBoundaryVanishing

/-! # Integrated Hodge Sheaf -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.IntegratedHodgeSheaf

noncomputable section

/-! The native class of the original integrated Hodge form has zero holomorphic image. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def manifoldIntegratedSection (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (⊤ : Opens M) 2) :
    ((Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M).X 2).obj.obj (op (⊤ : Opens M)) :=
  ((Abelian.ManifoldIntegration.abelianManifoldIntegration E M).f 2).hom.app (op (⊤ : Opens M)) form

theorem manifoldIntegratedSection_closed (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (⊤ : Opens M) 2)
    (hform : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d form = 0) :
    ((Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M).d 2 3).hom.app (op (⊤ : Opens M))
      (manifoldIntegratedSection E M form) = 0 := by
  apply Chern.Sheaf.AugmentedResolution.sheafCochainMap_section_closed (Abelian.ManifoldIntegration.abelianManifoldIntegration E M) 2 form
  rw [Abelian.ManifoldIntegration.abelianManifoldDeRhamComplex_d]
  exact hform

def manifoldIntegratedSheafClass (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (⊤ : Opens M) 2)
    (hform : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d form = 0) :
    CategoryTheory.Sheaf.H (Abelian.ManifoldDeRham.abelianLocallyConstantComplexSheaf (TopCat.of M)) 2 :=
  CategoryTheory.Sheaf.H.map (Manifold.SmoothZeroResolution.abelianManifoldSmoothZeroIso E M).inv 2
    (Intrinsic.SectionCohomologyMap.nativeSectionCohomologyMap (Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M) (Manifold.SmoothZeroResolution.abelianManifoldSmoothComplex_exact E M) 1
      ((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex (Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M)).homologyπ 2
        (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk 1 _ (manifoldIntegratedSection E M form) (manifoldIntegratedSection_closed E M form hform))))

theorem manifoldIntegratedSheafClass_eq_resolution
    (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (⊤ : Opens M) 2) (hform : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d form = 0) :
    manifoldIntegratedSheafClass E M form hform =
      CategoryTheory.Sheaf.H.map (Manifold.SmoothZeroResolution.abelianManifoldSmoothZeroIso E M).inv 2
        (Chern.Sheaf.ResolutionClasses.sheafResolutionCycleClass (Manifold.IntegrationConnecting.manifoldSmoothNativeResolution E M) 2
          (((Manifold.IntegrationConnecting.manifoldIntegrationNativeLift E M).f 2).hom.app (op (⊤ : Opens M)) form)
          (Manifold.IntegrationConnecting.manifoldIntegrationNativeLift_closed E M form hform)) := by
  exact congrArg (CategoryTheory.Sheaf.H.map (Manifold.SmoothZeroResolution.abelianManifoldSmoothZeroIso E M).inv 2)
    (Intrinsic.SectionCohomologyMap.nativeSectionCohomologyMap_class (Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M)
      (Manifold.SmoothZeroResolution.abelianManifoldSmoothComplex_exact E M) 1 (manifoldIntegratedSection E M form)
      (manifoldIntegratedSection_closed E M form hform))

theorem manifoldIntegratedSheafClass_eq_neg_connecting
    (s : (Manifold.DeRhamSecondQuotient.manifoldDeRhamSecondQuotient E M).obj.obj (op (⊤ : Opens M)))
    (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (⊤ : Opens M) 2) (hform : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d form = 0)
    (hs : (Manifold.DeRhamSecondQuotient.manifoldDeRhamSecondQuotientInclusion E M).hom.app (op (⊤ : Opens M)) s = form) :
    manifoldIntegratedSheafClass E M form hform = -Manifold.DeRhamSecondQuotient.manifoldDeRhamConnectingClass E M s := by
  let eH := (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology (TopCat.of M)) 2).mapIso
    (Manifold.SmoothZeroResolution.abelianManifoldSmoothZeroIso E M)
  have h := Manifold.IntegrationConnecting.manifoldDeRhamConnectingClass_integration E M s form hform hs
  have hn := congrArg (fun x => eH.inv x) h
  change eH.inv (eH.hom (Manifold.DeRhamSecondQuotient.manifoldDeRhamConnectingClass E M s)) =
    eH.inv (-Chern.Sheaf.ResolutionClasses.sheafResolutionCycleClass (Manifold.IntegrationConnecting.manifoldSmoothNativeResolution E M) 2
      (((Manifold.IntegrationConnecting.manifoldIntegrationNativeLift E M).f 2).hom.app (op (⊤ : Opens M)) form)
      (Manifold.IntegrationConnecting.manifoldIntegrationNativeLift_closed E M form hform)) at hn
  rw [eH.hom_inv_id_apply, map_neg] at hn
  change Manifold.DeRhamSecondQuotient.manifoldDeRhamConnectingClass E M s =
    -CategoryTheory.Sheaf.H.map (Manifold.SmoothZeroResolution.abelianManifoldSmoothZeroIso E M).inv 2
      (Chern.Sheaf.ResolutionClasses.sheafResolutionCycleClass (Manifold.IntegrationConnecting.manifoldSmoothNativeResolution E M) 2
        (((Manifold.IntegrationConnecting.manifoldIntegrationNativeLift E M).f 2).hom.app (op (⊤ : Opens M)) form)
        (Manifold.IntegrationConnecting.manifoldIntegrationNativeLift_closed E M form hform)) at hn
  rw [← manifoldIntegratedSheafClass_eq_resolution E M form hform] at hn
  exact (neg_neg (manifoldIntegratedSheafClass E M form hform)).symm.trans (congrArg Neg.neg hn.symm)

end

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem manifoldIntegratedHodgeClass_holomorphic_zero
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 2) (hform : Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree E M 1 1 form.val.val) :
    CategoryTheory.Sheaf.H.map (Manifold.DolbeaultComparison.locallyConstantComplexHolomorphicSheafMap (E := E) (M := M)) 2
      (manifoldIntegratedSheafClass E M (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ form.val)
        (by rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen_d, form.property, map_zero])) = 0 := by
  obtain ⟨s, hs, hzero⟩ := Manifold.HodgeBoundaryVanishing.exists_manifoldHodgeConnectingLift form hform
  rw [manifoldIntegratedSheafClass_eq_neg_connecting E M s _ _ hs]
  rw [map_neg, hzero, neg_zero]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.IntegratedHodgeSheaf
