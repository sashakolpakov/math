import OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection

/-! # Base Open Lift Analytic -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.BaseOpenLiftAnalytic.Constructions

noncomputable section

/-! The actual lift from an analytic open to an open subscheme is
holomorphic and has bijective native differential. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.IntrinsicGraphBaseProjection.Constructions.Intrinsic OAI.AlgebraicGeometry.CycleClass.Thom.Open.HolomorphicEmbeddingRestriction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential.Constructions.Manifold OAI.AlgebraicGeometry.CycleClass.Thom.HolomorphicHomeomorph.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y N : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral Y.left] [Smooth Y.hom]
  [IsIntegral N.left] [Smooth N.hom] (j : Y ⟶ N) [IsOpenImmersion j.left]
  (U : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N))
  (hU : (U : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints N)) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j))

local notation "MY" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ
local notation "MN" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension N.hom) → ℂ

abbrev sourceHomeomorph := Open.HolomorphicEmbeddingRestriction.Constructions.restrictedHomeomorph (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j)
  (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map j ω) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion j) U hU

theorem sourceHomeomorph_symm_analytic :
    ContMDiff 𝓘(ℂ, MN) 𝓘(ℂ, MY) ω (sourceHomeomorph j U hU).symm :=
  Open.HolomorphicEmbeddingRestriction.Constructions.restrictedHomeomorph_symm_analytic (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j) (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map j ω)
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion j) U hU
    (ComplexPoints.Analytic.IntrinsicOpenDifferential.mfderiv_nativeScheme_openImmersion_bijective j)

theorem baseOpenLift_analytic : ContMDiff 𝓘(ℂ, MN) 𝓘(ℂ, MY) ω (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) :=
  (show ContMDiff 𝓘(ℂ, MY) 𝓘(ℂ, MY) ω
    (Subtype.val : GraphOpenImmersion.Constructions.graphSourceOpen (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j) (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map j ω) U →
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) from contMDiff_subtype_val).comp
        (sourceHomeomorph_symm_analytic j U hU)

theorem baseOpenLift_differential_bijective (x : U) :
    Function.Bijective (mfderiv 𝓘(ℂ, MN) 𝓘(ℂ, MY) (IntrinsicGraphBaseProjection.Constructions.Intrinsic.baseOpenLift j U hU) x) := by
  have h := HolomorphicHomeomorph.Constructions.homeomorph_mfderiv_bijective (sourceHomeomorph j U hU).symm
    ((sourceHomeomorph_symm_analytic j U hU).mdifferentiable (by simp))
    ((Open.HolomorphicEmbeddingRestriction.Constructions.restrictedHomeomorph_analytic (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j) (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map j ω)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion j) U hU).mdifferentiable (by simp)) x
  have hd := ComplexPoints.Analytic.RegularLocusComplement.mfderiv_intoOpen_eq (𝕜 := ℂ) («E» := MN) (F := MY)
    (GraphOpenImmersion.Constructions.graphSourceOpen (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j) (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map j ω) U)
    (sourceHomeomorph j U hU).symm x
  exact (congrArg (fun L : MN →L[ℂ] MY => Function.Bijective L) hd).mp h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.BaseOpenLiftAnalytic.Constructions
