import OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticProductCharts
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.PresentationPoints

/-! # Analytic Product Maps -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticProductMaps.Constructions

noncomputable section

/-! Joint holomorphicity in the native manifold structures, including
both directions of the actual product-presentation point homeomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.Topology MonoidalCategory TensorProduct _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PointProduct.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticProductCharts.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.PresentationPoints.Constructions

variable {X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [IsIntegral Z.left] [Smooth Z.hom]

local notation "ModelX" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ
local notation "ModelY" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ
local notation "ModelZ" => Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Z.hom) → ℂ

theorem contMDiff_schemePairMap (φ : X ⊗ Y ⟶ Z) (r : ℕ∞ω) :
    ContMDiff (𝓘(ℂ, ModelX).prod 𝓘(ℂ, ModelY)) 𝓘(ℂ, ModelZ) r
      (fun xy : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y =>
        ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ (lift xy.1 xy.2)) := by
  apply contMDiff_iff.mpr
  refine ⟨(ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map φ).comp (Scheme.PointProduct.Constructions.schemePointPair_continuous X Y), ?_⟩
  rintro ⟨x₁, x₂⟩ y
  have h := AnalyticProductCharts.Constructions.contDiffOn_schemePairMap_regularCharts φ
    (chartAt ModelX x₁) (chartAt ModelY x₂) (chartAt ModelZ y)
    (chart_mem_atlas ModelX x₁) (chart_mem_atlas ModelY x₂) (chart_mem_atlas ModelZ y)
  simpa only [extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe,
    PartialEquiv.prod_target, extChartAt_coe, extChartAt_coe_symm, extChartAt_source,
    extChartAt_target, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ, Function.comp_def, id_eq, Set.preimage, Prod.map_apply,
    Set.mem_ofPred_eq, Set.ofPred_mem_eq]
    using h.of_le (show r ≤ ω from le_top)

theorem productPresentationPointsHomeomorph_contMDiff
    (πX : Z ⟶ X) (πY : Z ⟶ Y) (hprod : IsLimit (BinaryFan.mk πX πY)) (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, ModelZ) (𝓘(ℂ, ModelX).prod 𝓘(ℂ, ModelY)) r
      (Product.PresentationPoints.Constructions.productPresentationPointsHomeomorph X Y Z πX πY hprod) :=
  (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map πX r).prodMk (ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map πY r)

theorem productPresentationPointsHomeomorph_symm_contMDiff
    (πX : Z ⟶ X) (πY : Z ⟶ Y) (hprod : IsLimit (BinaryFan.mk πX πY)) (r : ℕ∞ω) :
    ContMDiff (𝓘(ℂ, ModelX).prod 𝓘(ℂ, ModelY)) 𝓘(ℂ, ModelZ) r
      (Product.PresentationPoints.Constructions.productPresentationPointsHomeomorph X Y Z πX πY hprod).symm :=
  contMDiff_schemePairMap (Product.PresentationPoints.Constructions.productPresentationPairMap X Y Z πX πY hprod) r

end

end OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticProductMaps.Constructions
