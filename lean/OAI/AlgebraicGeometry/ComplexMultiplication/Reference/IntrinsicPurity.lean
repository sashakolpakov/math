import OAI.AlgebraicGeometry.ComplexMultiplication.ReferenceCanonicalClosedForms
import OAI.Analysis.DifferentialForms.Manifold.PurePullback

/-! # Intrinsic Purity -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.IntrinsicPurity

noncomputable section

/-! # Original F¹ classes have the genuine native holomorphic Hodge type -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "N" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "G" => OAI.AlgebraicGeometry.ComplexMultiplication.AnalyticIntrinsicAtlasRegular.NativePointManifold X
local notation "M" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X

/-- The same actual closed original form, transported by the proved analytic identity. -/
def originalClosedHolomorphicNativeForm (p : ℕ)
    (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (Opposite.op ⊤))
    (hθ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).hom.app (Opposite.op ⊤) θ = 0) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms N G p :=
  Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback (IntrinsicReferenceAtlasComparison.nativePointManifoldRealDiffeomorph X)
    (IntrinsicReferenceAtlasComparison.nativePointManifoldRealDiffeomorph X).contMDiff p
      (ReferenceCanonicalClosedForms.originalClosedHolomorphicSmoothForm X p θ hθ)

/-- Its actual tangent-action character is the native pure holomorphic character. -/
theorem originalClosedHolomorphicNativeForm_pure (p : ℕ)
    (θ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheaf X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).presheaf.obj (Opposite.op ⊤))
    (hθ : (ComplexPoint.Basic.ComplexSchemePoint.holomorphicDeRhamSheafDifferential X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) p).hom.app (Opposite.op ⊤) θ = 0) :
    Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree N G p 0
      (originalClosedHolomorphicNativeForm X p θ hθ).val.val :=
  Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree.pullback
    (ReferenceSmooth.Local.originalHolomorphicSheafToGlobalSmoothForm_pure X p θ)
      (AnalyticIntrinsicAtlasRegular.nativePointManifoldHomeomorph X) (AnalyticIntrinsicAtlasRegular.contMDiff_nativePointManifoldHomeomorph X ∞)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse atlas cohomology comparison retains the literal pullback of closed forms. -/
theorem nativeOriginalDeRhamCohomologyIso_inv_formClass (p : ℕ)
    (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M p) :
    (IntrinsicReferenceCanonicalComparison.nativeOriginalDeRhamCohomologyIso X p).inv
        (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M p form) =
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass N G p
        (Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback (IntrinsicReferenceAtlasComparison.nativePointManifoldRealDiffeomorph X)
          (IntrinsicReferenceAtlasComparison.nativePointManifoldRealDiffeomorph X).contMDiff p form) := by
  change Analysis.DifferentialForms.Manifold.ManifoldDeRhamPullback.manifoldDeRhamCohomologyPullback (IntrinsicReferenceAtlasComparison.nativePointManifoldRealDiffeomorph X)
    (IntrinsicReferenceAtlasComparison.nativePointManifoldRealDiffeomorph X).contMDiff p
      (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M p form) = _
  exact Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldDeRhamFormClass_pullback_apply (IntrinsicReferenceAtlasComparison.nativePointManifoldRealDiffeomorph X)
    (IntrinsicReferenceAtlasComparison.nativePointManifoldRealDiffeomorph X).contMDiff p form

variable [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

local notation "V" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalIntegralProjectiveVariety X

set_option backward.isDefEq.respectTransparency false in
/-- Membership in original F¹ implies membership in the actual canonical native H¹⁰. -/
theorem originalF1_mem_implies_nativePure
    (z : (V).complexCohomology 1)
    (hz : ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X 1
      ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X 1).symm
        (BettiBridge.schemeConstantCohomologyBridgeEquiv ℂ X 1 z)) ∈
          ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltrationComplexSubmodule X 1 1) :
    z ∈ (V).pureBettiSubspace 1 0 := by
  let a := ((V).deRhamBettiIso 1).toLinearEquiv.symm z
  have hb : ((V).deRhamBettiIso 1).hom a = z :=
    ((V).deRhamBettiIso 1).toLinearEquiv.apply_symm_apply z
  have hF : ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X 1
      ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X 1).symm
        (BettiBridge.schemeConstantCohomologyBridgeEquiv ℂ X 1 (((V).deRhamBettiIso 1).hom a))) ∈
          ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltrationComplexSubmodule X 1 1 := by
    rw [hb]
    exact hz
  obtain ⟨θ, hθ, he⟩ := (CanonicalGlobalNormalization.originalF1_mem_iff_nativeCanonicalForm X a).mp hF
  have hc := ReferenceCanonicalClosedForms.originalClosedHolomorphicGlobalClass_native_form X 1 θ hθ
  have hd := congrArg (IntrinsicReferenceCanonicalComparison.nativeOriginalDeRhamCohomologyIso X 1).toLinearEquiv.symm (he.trans hc)
  change (IntrinsicReferenceCanonicalComparison.nativeOriginalDeRhamCohomologyIso X 1).toLinearEquiv.symm
      ((IntrinsicReferenceCanonicalComparison.nativeOriginalDeRhamCohomologyIso X 1).toLinearEquiv a) =
    (IntrinsicReferenceCanonicalComparison.nativeOriginalDeRhamCohomologyIso X 1).toLinearEquiv.symm
      (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M 1
        (ReferenceCanonicalClosedForms.originalClosedHolomorphicSmoothForm X 1 θ hθ)) at hd
  simp only [LinearEquiv.symm_apply_apply] at hd
  have hi := nativeOriginalDeRhamCohomologyIso_inv_formClass X 1
    (ReferenceCanonicalClosedForms.originalClosedHolomorphicSmoothForm X 1 θ hθ)
  have ha : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass N G 1
      (originalClosedHolomorphicNativeForm X 1 θ hθ) = a := hi.symm.trans hd.symm
  refine ((V).mem_pureBettiSubspace_iff 1 0 z).mpr
    ⟨originalClosedHolomorphicNativeForm X 1 θ hθ,
      originalClosedHolomorphicNativeForm_pure X 1 θ hθ, ?_⟩
  change ((V).deRhamBettiIso 1).hom
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass N G 1 (originalClosedHolomorphicNativeForm X 1 θ hθ)) = z
  rw [ha]
  exact hb

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.IntrinsicPurity
