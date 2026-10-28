import OAI.AlgebraicGeometry.Divisors.LineBundles.PresentationComponentSupportClass
import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.CycleClass

/-! # Presentation Canonical Generator -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.PresentationCanonicalGenerator.BundleCycles

noncomputable section

/-! The canonical smooth-scheme class of every support equals the presentation's independently assembled geometric fundamental-cycle class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier] (p : ℕ)

omit [AlgebraicGeometry.IsIntegral X.carrier] in
theorem presentationComponent_geometricGenerator
    (C : irreducibleComponents X.carrier)
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport (X.componentVariety C) p) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) (X.componentInclusionOver C)
      (X.geometricCycleClassMap p (Finsupp.single ((X.componentDimensionSupportEquiv p).symm ⟨C, Z⟩) 1)) =
      Z.geometricCycleClass := by
  have h := (X.componentBettiEquiv_apply (ModuleCat.of ℚ ℚ) (p + p)
    (X.geometricCycleClassMap p (Finsupp.single ((X.componentDimensionSupportEquiv p).symm ⟨C, Z⟩) 1)) C).symm.trans
      (X.componentBettiEquiv_geometricCycleClassMap p _ C)
  rw [X.componentDimensionCycleEquiv_single_same, Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_single,
    one_smul] at h
  exact h

theorem presentationComponent_canonicalGenerator
    (C : irreducibleComponents X.carrier)
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport (X.componentVariety C) p) :
    Scheme.AbsoluteCycleClass.BundleCycles.schemeCycleClass X.toOver (X.componentSupportImage C Z.val) p (PresentationComponentSupportClass.BundleCycles.componentImageSupport_codimension X p C Z) =
      X.geometricCycleClassMap p (Finsupp.single ((X.componentDimensionSupportEquiv p).symm ⟨C, Z⟩) 1) := by
  apply X.componentBetti_ext (ModuleCat.of ℚ ℚ) (p + p)
  intro D
  have hD := PresentationComponentSupportClass.BundleCycles.integralPresentation_components_equal X D C
  subst D
  exact (PresentationComponentSupportClass.BundleCycles.componentImageSupport_cycleClass X p C Z).trans (presentationComponent_geometricGenerator X p C Z).symm

theorem integralPresentation_cycleSupportClass (Z : X.DimensionCycleSupport p) :
    Scheme.AbsoluteCycleClass.BundleCycles.schemeCycleClass X.toOver Z.val p (PresentationComponentSupportClass.BundleCycles.integralPresentationSupport_dimension X p Z) =
      X.geometricCycleClassMap p (Finsupp.single Z 1) := by
  obtain ⟨⟨C, W⟩, rfl⟩ := (X.componentDimensionSupportEquiv p).symm.surjective Z
  exact presentationComponent_canonicalGenerator X p C W

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.PresentationCanonicalGenerator.BundleCycles
