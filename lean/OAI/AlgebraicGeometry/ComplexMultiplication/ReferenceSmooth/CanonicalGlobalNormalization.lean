import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CanonicalGlobalNormalization

/-! # Canonical Global Normalization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.CanonicalGlobalNormalization

noncomputable section

/-! # The unchanged canonical comparison on arbitrary smooth global classes

All degree maps are the actual smooth-simplex integration maps already used
by the original holomorphic comparison.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "Y" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
local notation "ΓInt" => Functor.mapHomologicalComplex
  (AlgebraicTopology.Sheaf.FlasqueBoundedBelow.TopCat.IsFlasque.BoundedBelowComplex.globalSectionsFunctor Y) (ComplexShape.up ℤ)

set_option backward.isDefEq.respectTransparency false in
/-- The actual smooth global class has the original normalized integration hyperclass. -/
theorem originalSmoothGlobalIntegration_hyperClass (n : ℤ)
    (w : (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt Y (Integration.originalSmoothDeRhamComplexInt X)).homology n) :
    Integration.originalSmoothIntegrationHypercohomologyAddEquiv X n
        (GlobalNaturality.globalSectionsToHypercohomology X (Integration.originalSmoothDeRhamComplexInt X) n w) =
      GlobalClassComparison.originalSmoothAmbientHyperClass X n
        (HomologicalComplex.homologyMap (Reference.GlobalIntegrationClasses.originalManifoldSimplexIntegrationInt X) n
          (HomologicalComplex.homologyMap (GlobalForms.originalSmoothGlobalSectionsIntIso X).hom n w)) := by
  have hs : (ΓInt).map (Integration.originalSmoothIntegrationSheafComplexInt X) =
      (GlobalForms.originalSmoothGlobalSectionsIntIso X).hom ≫
        (Reference.GlobalIntegrationClasses.originalManifoldSimplexIntegrationInt X ≫ Reference.GlobalIntegrationClasses.originalSmoothGlobalUnitInt X) := by
    have h := congrArg (fun f => (GlobalForms.originalSmoothGlobalSectionsIntIso X).hom ≫ f)
      (Reference.GlobalIntegrationClasses.originalGlobalIntegrationInt_square X)
    simpa only [Iso.hom_inv_id_assoc] using! h
  rw [Integration.originalSmoothIntegrationHypercohomologyAddEquiv_apply,
    ← GlobalNaturality.globalSectionsToHypercohomology_naturality, hs,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
  rfl

variable [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

set_option backward.isDefEq.respectTransparency false in
/-- The exact original comparison equals a smooth global class precisely when their integrals agree. -/
theorem originalOrdinarySmoothGlobalClass_iff (n : ℕ)
    (z : (Reference.OrdinarySmoothGlobalUnits.originalOrdinaryAmbientCochainsInt X).homology (n : ℤ))
    (w : (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt Y (Integration.originalSmoothDeRhamComplexInt X)).homology
      (n : ℤ)) :
    Hypercohomology.originalDeRhamSmoothHypercohomologyAddEquiv X (n : ℤ)
        (ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X (n : ℤ)
          ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X n).symm
            (GlobalClassComparison.originalOrdinaryConstantCohomologyAddEquiv X n z))) =
      GlobalNaturality.globalSectionsToHypercohomology X (Integration.originalSmoothDeRhamComplexInt X) (n : ℤ) w ↔
    HomologicalComplex.homologyMap (Reference.OrdinarySmoothGlobalUnits.originalOrdinaryToSmoothAmbientInt X) (n : ℤ) z =
      HomologicalComplex.homologyMap (Reference.GlobalIntegrationClasses.originalManifoldSimplexIntegrationInt X) (n : ℤ)
        (HomologicalComplex.homologyMap (GlobalForms.originalSmoothGlobalSectionsIntIso X).hom (n : ℤ) w) := by
  let i := Integration.originalSmoothIntegrationHypercohomologyAddEquiv X (n : ℤ)
  have hs := GlobalClassComparison.originalSmoothAmbientHyperClass_bijective X n
  have hz := GlobalClassComparison.originalOrdinaryConstantDeRhamIntegration_hyperClass X n z
  have hw := originalSmoothGlobalIntegration_hyperClass X (n : ℤ) w
  constructor
  · intro h
    apply hs.1
    exact hz.symm.trans ((congrArg i h).trans hw)
  · intro h
    apply i.injective
    exact hz.trans ((congrArg (GlobalClassComparison.originalSmoothAmbientHyperClass X (n : ℤ)) h).trans hw.symm)

local notation "V" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalIntegralProjectiveVariety X

set_option backward.isDefEq.respectTransparency false in
/-- The original comparison on smooth global classes retains the actual native de Rham normalization. -/
theorem originalCanonicalSmoothGlobalClass_iff (n : ℕ)
    (a : (V).deRhamCohomology n)
    (w : (Cohomology.GlobalSections.TopCat.Sheaf.globalSectionsComplexInt Y (Integration.originalSmoothDeRhamComplexInt X)).homology
      (n : ℤ)) :
    Hypercohomology.originalDeRhamSmoothHypercohomologyAddEquiv X (n : ℤ)
        (ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X (n : ℤ)
          ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X n).symm
            (Reference.BettiBridge.schemeConstantCohomologyBridgeEquiv ℂ X n (((V).deRhamBettiIso n).hom a)))) =
      GlobalNaturality.globalSectionsToHypercohomology X (Integration.originalSmoothDeRhamComplexInt X) (n : ℤ) w ↔
    (IntrinsicReferenceCanonicalComparison.nativeOriginalDeRhamCohomologyIso X n).hom a =
      (Reference.CanonicalGlobalNormalization.originalManifoldIntegerDeRhamCohomologyIso X n).hom
        (HomologicalComplex.homologyMap (GlobalForms.originalSmoothGlobalSectionsIntIso X).hom (n : ℤ) w) := by
  rw [← Reference.CanonicalGlobalNormalization.originalOrdinaryIntegerClass_constant]
  rw [originalOrdinarySmoothGlobalClass_iff]
  have hs : Function.Injective (Reference.CanonicalGlobalNormalization.originalManifoldIntegerSmoothCohomologyIso X n).hom :=
    (Reference.CanonicalGlobalNormalization.originalManifoldIntegerSmoothCohomologyIso X n).addCommGroupIsoToAddEquiv.injective
  rw [← hs.eq_iff, Reference.CanonicalGlobalNormalization.originalManifoldIntegerRestriction_normalization,
    Reference.CanonicalGlobalNormalization.originalManifoldIntegerIntegration_normalization]
  have hi := (Reference.CanonicalSingularGlobalClasses.originalOrdinaryAmbientIntegerCohomologyIso X n).addCommGroupIsoToAddEquiv.apply_symm_apply
    ((IntrinsicReferenceCanonicalComparison.nativeOriginalOrdinaryCohomologyIso X n).hom (((V).deRhamBettiIso n).hom a))
  simp only [Iso.addCommGroupIsoToAddEquiv_apply] at hi
  dsimp only [Reference.CanonicalGlobalNormalization.originalOrdinaryIntegerClass]
  rw [hi]
  exact (IntrinsicReferenceCanonicalComparison.nativeOriginalCanonicalComparison_iff X n a _).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceSmooth.CanonicalGlobalNormalization
