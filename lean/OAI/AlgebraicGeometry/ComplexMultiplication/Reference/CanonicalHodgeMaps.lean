import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.TensorComparison
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.Canonical
import OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalAbelianWeightOne
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.FiltrationPullback
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport

/-! # Canonical Hodge Maps -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CanonicalHodgeMaps

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

/-! # Original filtration endomorphisms are canonical rational Hodge maps -/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint
open scoped TensorProduct

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] [GrpObj X]

local instance CMOriginalCanonicalHodgeMaps.localInstance1 : Algebra ℚ (Module.End ℚ H^1(X; ℚ)) :=
  Module.End.instAlgebra ℚ ℚ H^1(X; ℚ)

/-- The original tensor filtration is exactly the canonical (1,0) Betti subspace. -/
theorem h1Comparison_mem_iff_schemeNativePure
    (z : ℂ ⊗[ℚ] Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X 1) :
    Definitions.h1Comparison X ((BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X 1).toLinearMap.baseChange ℂ z) ∈
        ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltrationComplexSubmodule X 1 1 ↔
      CohomologyBaseChange.CM.singularCohomologyComplexification
        (Betti.Scheme.schemePointSpace X) 1 z ∈
          (BundledAbelianBridge.originalIntegralProjectiveVariety X).pureBettiSubspace 1 0 := by
  rw [TensorComparison.h1Comparison_schemeBetti]
  exact Canonical.originalF1_mem_iff_nativePure X _

omit [GrpObj X] in
/-- Scalar extension retains conjugation by the actual rational Betti bridge. -/
theorem schemeBetti_conjugate_baseChange (u : Module.End ℚ H^1(X; ℚ))
    (z : ℂ ⊗[ℚ] Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X 1) :
    (BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X 1).toLinearMap.baseChange ℂ
        (((BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X 1).symm.conjAlgEquiv ℚ u).baseChange ℂ z) =
      u.baseChange ℂ ((BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X 1).toLinearMap.baseChange ℂ z) := by
  let e := BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X 1
  let uB := e.symm.conjAlgEquiv ℚ u
  have he : e.toLinearMap.comp uB = u.comp e.toLinearMap := by
    ext v
    simp only [uB, LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
  calc
    _ = (e.toLinearMap.comp uB).baseChange ℂ z :=
      (LinearMap.congr_fun (LinearMap.baseChange_comp (A := ℂ)
        (f := uB) e.toLinearMap) z).symm
    _ = (u.comp e.toLinearMap).baseChange ℂ z :=
      congrArg (fun f => f.baseChange ℂ z) he
    _ = _ := LinearMap.congr_fun
      (LinearMap.baseChange_comp (A := ℂ) (f := e.toLinearMap) u) z

set_option backward.isDefEq.respectTransparency false in
/-- Canonical holomorphic membership is the literal pure Betti condition. -/
theorem originalCanonicalH1_mem_holomorphic_iff
    (z : ℂ ⊗[ℚ] Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X 1) :
    z ∈ (CanonicalAbelianWeightOne.originalCanonicalH1 X).holomorphic ↔
      CohomologyBaseChange.CM.singularCohomologyComplexification
        (Betti.Scheme.schemePointSpace X) 1 z ∈
          (BundledAbelianBridge.originalIntegralProjectiveVariety X).pureBettiSubspace 1 0 := Iff.rfl

set_option backward.isDefEq.respectTransparency false in
/-- Literal preservation of the pure piece gives a map of the canonical Hodge structure. -/
theorem originalCanonicalH1_isHodgeMap_of_pure
    (v : Module.End ℚ (Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X 1))
    (hv : ∀ z : ℂ ⊗[ℚ] Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X 1,
      CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X) 1 z ∈
          (BundledAbelianBridge.originalIntegralProjectiveVariety X).pureBettiSubspace 1 0 →
      CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X) 1
          (v.baseChange ℂ z) ∈ (BundledAbelianBridge.originalIntegralProjectiveVariety X).pureBettiSubspace 1 0) :
    WeightOne.CM.IsHodgeMap (CanonicalAbelianWeightOne.originalCanonicalH1 X) (CanonicalAbelianWeightOne.originalCanonicalH1 X) v := by
  intro z hz
  exact (originalCanonicalH1_mem_holomorphic_iff X (v.baseChange ℂ z)).mpr
    (hv z ((originalCanonicalH1_mem_holomorphic_iff X z).mp hz))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Intertwining the rational action transfers original filtration preservation. -/
theorem h1HodgeMap_of_intertwines
    (u : Module.End ℚ H^1(X; ℚ))
    (v : Module.End ℚ (Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) X 1))
    (hu : u ∈ Hodge.Endomorphisms.h1HodgeEndomorphismAlgebra X)
    (he : (BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X 1).toLinearMap.comp v =
      u.comp (BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X 1).toLinearMap) :
    WeightOne.CM.IsHodgeMap (CanonicalAbelianWeightOne.originalCanonicalH1 X) (CanonicalAbelianWeightOne.originalCanonicalH1 X) v := by
  apply originalCanonicalH1_isHodgeMap_of_pure X v
  intro z hz
  let e := BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X 1
  have hzO := (h1Comparison_mem_iff_schemeNativePure X z).mpr hz
  have hp := (FiltrationPullback.mem_h1HodgeEndomorphismAlgebra_iff X u).mp hu
    (e.toLinearMap.baseChange ℂ z) hzO
  change Definitions.h1Comparison X (u.baseChange ℂ (e.toLinearMap.baseChange ℂ z)) ∈
    ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltrationComplexSubmodule X 1 1 at hp
  have hv : e.toLinearMap.baseChange ℂ (v.baseChange ℂ z) =
      u.baseChange ℂ (e.toLinearMap.baseChange ℂ z) := by
    calc
      _ = (e.toLinearMap.comp v).baseChange ℂ z :=
        (LinearMap.congr_fun (LinearMap.baseChange_comp (A := ℂ)
          (f := v) e.toLinearMap) z).symm
      _ = (u.comp e.toLinearMap).baseChange ℂ z :=
        congrArg (fun f => f.baseChange ℂ z) he
      _ = _ := LinearMap.congr_fun
        (LinearMap.baseChange_comp (A := ℂ) (f := e.toLinearMap) u) z
  have hprop := congrArg
    (fun t : ℂ ⊗[ℚ] H^1(X; ℚ) =>
      Definitions.h1Comparison X t ∈ ComplexPoint.Basic.ComplexSchemePoint.hodgeFiltrationComplexSubmodule X 1 1) hv.symm
  have hout := Eq.mp hprop hp
  exact (h1Comparison_mem_iff_schemeNativePure X (v.baseChange ℂ z)).mp hout

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every original F¹-preserving rational action is an actual canonical Hodge map. -/
theorem h1HodgeEndomorphism_is_canonicalHodgeMap
    (u : Module.End ℚ H^1(X; ℚ)) (hu : u ∈ Hodge.Endomorphisms.h1HodgeEndomorphismAlgebra X) :
    WeightOne.CM.IsHodgeMap (CanonicalAbelianWeightOne.originalCanonicalH1 X) (CanonicalAbelianWeightOne.originalCanonicalH1 X)
      ((BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X 1).symm.conjAlgEquiv ℚ u) := by
  apply h1HodgeMap_of_intertwines X u _ hu
  ext z
  simp only [LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CanonicalHodgeMaps
