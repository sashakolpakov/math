import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.IntrinsicPurity
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.AbelianInvariantClosed
import OAI.AlgebraicGeometry.AbelianVariety.PureAverage
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.PureCovectorsOf

/-! # Canonical -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.Canonical

noncomputable section

section

/-! # Actual native invariant representatives of original holomorphic classes -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

/-- The actual one-variable alternating covector is recovered from its pure complex functional. -/
theorem complexLinearCovector_complexLinearOfPure
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] (β : E [⋀^Fin 1]→L[ℝ] ℂ)
    (hβ : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 0 β) :
    Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E (HodgeConjecture.DegreeTwo.PureCovectorsOf.Constructions.PureCovectors.complexLinearOfPure β hβ) = β := by
  ext v
  change β (fun _ => v 0) = β v
  apply congrArg β
  funext i
  exact congrArg v (Subsingleton.elim 0 i)

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] [GrpObj X]

local notation "N" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "Native" => OAI.AlgebraicGeometry.ComplexMultiplication.AnalyticIntrinsicAtlasRegular.NativePointManifold X
local notation "V" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalIntegralProjectiveVariety X

set_option backward.isDefEq.respectTransparency false in
/-- The original global representative pulls back to the same actual native invariant form. -/
theorem originalAbelianInvariantGlobalSection_native_form (α : N →L[ℂ] ℂ) :
    (IntrinsicPurity.originalClosedHolomorphicNativeForm X 1
      (AbelianInvariantGlobal.originalAbelianInvariantGlobalSection X α)
      (AbelianInvariantClosed.originalAbelianInvariantGlobalSection_closed X α)).val =
        AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantSmoothForm (InvariantPullback.complexInvariantIdentityCovector (G := Native) α) := by
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (IntrinsicReferenceAtlasComparison.nativePointManifoldRealDiffeomorph X)
      (IntrinsicReferenceAtlasComparison.nativePointManifoldRealDiffeomorph X).contMDiff
      (ReferenceSmooth.Local.originalHolomorphicSheafToGlobalSmoothForm X 1
        (AbelianInvariantGlobal.originalAbelianInvariantGlobalSection X α)) = _
  rw [AbelianInvariantGlobal.originalAbelianInvariantGlobalSection_smooth]
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (AnalyticIntrinsicAtlasRegular.nativePointManifoldHomeomorph X)
      (IntrinsicReferenceAtlasComparison.nativePointManifoldHomeomorph_realSmooth X)
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (AnalyticIntrinsicAtlasRegular.nativePointManifoldHomeomorph X).symm
        (IntrinsicReferenceAtlasComparison.nativePointManifoldHomeomorph_symm_realSmooth X)
        (AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantSmoothForm (InvariantPullback.complexInvariantIdentityCovector (G := Native) α))) = _
  rw [← Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_comp]
  have he : (AnalyticIntrinsicAtlasRegular.nativePointManifoldHomeomorph X).symm ∘
      (AnalyticIntrinsicAtlasRegular.nativePointManifoldHomeomorph X) = (id : Native → Native) :=
    funext (AnalyticIntrinsicAtlasRegular.nativePointManifoldHomeomorph X).symm_apply_apply
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  change ((AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantSmoothForm (InvariantPullback.complexInvariantIdentityCovector (G := Native) α) :
      Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm N Native 1).pullback
        ((AnalyticIntrinsicAtlasRegular.nativePointManifoldHomeomorph X).symm ∘ (AnalyticIntrinsicAtlasRegular.nativePointManifoldHomeomorph X))) x = _
  rw [he, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.pullback_id]

set_option backward.isDefEq.respectTransparency false in
/-- The invariant chart equivalence uses precisely the original constructed identity covector. -/
theorem invariantChartEvalEquiv_symm_complexLinearCovector (α : N →L[ℂ] ℂ) :
    ((AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv (E := N) (G := Native) 1).symm
      (Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector N α)).val =
        AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantSmoothForm (InvariantPullback.complexInvariantIdentityCovector (G := Native) α) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual canonical Betti class of a model covector is the class of its original section. -/
theorem originalAbelianInvariantGlobalSection_canonical_betti (α : N →L[ℂ] ℂ) :
    AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv (BundledAbelianBridge.originalAbelianVariety X) 1
        (Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector N α) =
      ((V).deRhamBettiIso 1).hom
        (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass N Native 1
          (IntrinsicPurity.originalClosedHolomorphicNativeForm X 1
            (AbelianInvariantGlobal.originalAbelianInvariantGlobalSection X α)
            (AbelianInvariantClosed.originalAbelianInvariantGlobalSection_closed X α))) := by
  change ((V).deRhamBettiIso 1).hom
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass N Native 1
      (AbelianVariety.InvariantCohomology.Constructions.Exterior.invariantClosedInclusion 1
        ((AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv (E := N) (G := Native) 1).symm
          (Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector N α)))) = _
  apply congrArg ((V).deRhamBettiIso 1).hom
  apply congrArg (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass N Native 1)
  apply Subtype.ext
  exact (invariantChartEvalEquiv_symm_complexLinearCovector X α).trans
    (originalAbelianInvariantGlobalSection_native_form X α).symm

end

/-! # The unchanged original F¹ is the actual canonical holomorphic H¹ subspace -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] [GrpObj X]

local notation "N" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "G" => OAI.AlgebraicGeometry.ComplexMultiplication.AnalyticIntrinsicAtlasRegular.NativePointManifold X
local notation "M" => OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X
local notation "V" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalIntegralProjectiveVariety X

set_option backward.isDefEq.respectTransparency false in
/-- Every actual canonical native (1,0) Betti class has an original closed holomorphic representative. -/
theorem nativePure_mem_implies_originalF1
    (z : (V).complexCohomology 1) (hz : z ∈ (V).pureBettiSubspace 1 0) :
    ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X 1
      ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X 1).symm
        (BettiBridge.schemeConstantCohomologyBridgeEquiv ℂ X 1 z)) ∈
          ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltrationComplexSubmodule X 1 1 := by
  let β := (AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv (BundledAbelianBridge.originalAbelianVariety X) 1).symm z
  have hb : AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv (BundledAbelianBridge.originalAbelianVariety X) 1 β = z :=
    (AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv (BundledAbelianBridge.originalAbelianVariety X) 1).apply_symm_apply z
  have hβ : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree N 1 0 β :=
    (AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv_pure (BundledAbelianBridge.originalAbelianVariety X) 1 0 β).mp (hb.symm ▸ hz)
  let α := HodgeConjecture.DegreeTwo.PureCovectorsOf.Constructions.PureCovectors.complexLinearOfPure β hβ
  have hα : Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector N α = β := complexLinearCovector_complexLinearOfPure β hβ
  let θ := AbelianInvariantGlobal.originalAbelianInvariantGlobalSection X α
  have hθ := AbelianInvariantClosed.originalAbelianInvariantGlobalSection_closed X α
  let a := ((V).deRhamBettiIso 1).toLinearEquiv.symm z
  have hab : ((V).deRhamBettiIso 1).hom a = z :=
    ((V).deRhamBettiIso 1).toLinearEquiv.apply_symm_apply z
  have hclass : ((V).deRhamBettiIso 1).hom
      (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass N G 1 (IntrinsicPurity.originalClosedHolomorphicNativeForm X 1 θ hθ)) = z := by
    have h := originalAbelianInvariantGlobalSection_canonical_betti X α
    rw [hα, hb] at h
    exact h.symm
  have ha : a = Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass N G 1
      (IntrinsicPurity.originalClosedHolomorphicNativeForm X 1 θ hθ) :=
    ((V).deRhamBettiIso 1).toLinearEquiv.injective (hab.trans hclass.symm)
  have hi := IntrinsicPurity.nativeOriginalDeRhamCohomologyIso_inv_formClass X 1
    (ReferenceCanonicalClosedForms.originalClosedHolomorphicSmoothForm X 1 θ hθ)
  have he : (IntrinsicReferenceCanonicalComparison.nativeOriginalDeRhamCohomologyIso X 1).hom a =
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass E M 1 (ReferenceCanonicalClosedForms.originalClosedHolomorphicSmoothForm X 1 θ hθ) := by
    apply (IntrinsicReferenceCanonicalComparison.nativeOriginalDeRhamCohomologyIso X 1).toLinearEquiv.symm.injective
    change (IntrinsicReferenceCanonicalComparison.nativeOriginalDeRhamCohomologyIso X 1).toLinearEquiv.symm
        ((IntrinsicReferenceCanonicalComparison.nativeOriginalDeRhamCohomologyIso X 1).toLinearEquiv a) = _
    rw [LinearEquiv.symm_apply_apply]
    exact ha.trans hi.symm
  have hc := ReferenceCanonicalClosedForms.originalClosedHolomorphicGlobalClass_native_form X 1 θ hθ
  have hf := (CanonicalGlobalNormalization.originalF1_mem_iff_nativeCanonicalForm X a).mpr
    ⟨θ, hθ, he.trans hc.symm⟩
  rw [hab] at hf
  exact hf

/-- Exact original/canonical identification, with no CM or compatibility premise. -/
theorem originalF1_mem_iff_nativePure (z : (V).complexCohomology 1) :
    ComplexPoint.Basic.ComplexSchemePoint.complexConstantCohomologyDeRhamAddEquiv X 1
      ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℂ X 1).symm
        (BettiBridge.schemeConstantCohomologyBridgeEquiv ℂ X 1 z)) ∈
          ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltrationComplexSubmodule X 1 1 ↔
      z ∈ (V).pureBettiSubspace 1 0 :=
  ⟨IntrinsicPurity.originalF1_mem_implies_nativePure X z, nativePure_mem_implies_originalF1 X z⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.Canonical
