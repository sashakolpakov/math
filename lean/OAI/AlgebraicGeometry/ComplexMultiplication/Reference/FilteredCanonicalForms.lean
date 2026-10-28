import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredGlobalForms
import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.CanonicalGlobalNormalization

/-! # Filtered Canonical Forms -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredCanonicalForms

noncomputable section

/-! # Original filtered classes retain their actual smooth closed representatives -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

local notation "Model" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "M" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X
local notation "Y" => TopCat.of M
local notation "ΓInt" => Functor.mapHomologicalComplex
  (AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y) (ComplexShape.up ℤ)
local notation "V" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalIntegralProjectiveVariety X

set_option backward.isDefEq.respectTransparency false in
/-- Every original filtered class is represented by a closed form in the actual smooth filtration. -/
theorem originalFiltered_mem_implies_canonicalFilteredForm (p n : ℕ)
    (a : (V).deRhamCohomology n)
    (ha : ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X (n : ℤ)
      ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X n).symm
        (BettiBridge.schemeConstantCohomologyBridgeEquiv ℂ X n (((V).deRhamBettiIso n).hom a))) ∈
          ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltration X p (n : ℤ)) :
    ∃ form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms Model M n,
      form.val ∈ Comparison.Betti.ManifoldFormFiltration.Hodge.manifoldFormFiltration Model M n p ∧
      (IntrinsicReferenceCanonicalComparison.nativeOriginalDeRhamCohomologyIso X n).hom a =
        Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass Model M n form := by
  obtain ⟨z, hz⟩ := FilteredSmoothMap.originalHodgeFiltration_filteredSmoothRepresentative X p (n : ℤ) _ ha
  let K := Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt Y (FilteredSmoothInt.originalFilteredSmoothComplexInt X p)
  obtain ⟨c, hc⟩ := (AddCommGrpCat.epi_iff_surjective (K.homologyπ (n : ℤ))).1 inferInstance z
  let w := HomologicalComplex.homologyMap
    ((ΓInt).map (FilteredSmoothInt.originalFilteredSmoothInclusionInt X p)) (n : ℤ) z
  have hw := (ReferenceSmooth.CanonicalGlobalNormalization.originalCanonicalSmoothGlobalClass_iff X n a w).mp hz
  refine ⟨FilteredGlobalForms.originalFilteredGlobalCycleForm X p n c,
    FilteredGlobalForms.originalFilteredGlobalCycleForm_filtered X p n c, ?_⟩
  rw [← FilteredGlobalForms.originalFilteredGlobalCycleForm_class]
  have hm := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyMap_comp
      ((ΓInt).map (FilteredSmoothInt.originalFilteredSmoothInclusionInt X p))
        (ReferenceSmooth.GlobalForms.originalSmoothGlobalSectionsIntIso X).hom (n : ℤ)) (K.homologyπ (n : ℤ) c)
  simp only [AddCommGrpCat.comp_apply] at hm
  change (IntrinsicReferenceCanonicalComparison.nativeOriginalDeRhamCohomologyIso X n).hom a =
    (CanonicalGlobalNormalization.originalManifoldIntegerDeRhamCohomologyIso X n).hom
      (HomologicalComplex.homologyMap
        (((ΓInt).map (FilteredSmoothInt.originalFilteredSmoothInclusionInt X p)) ≫
          (ReferenceSmooth.GlobalForms.originalSmoothGlobalSectionsIntIso X).hom) (n : ℤ)
            (K.homologyπ (n : ℤ) c))
  rw [hm, hc]
  exact hw

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FilteredCanonicalForms
