import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericFibers

/-! # Open Range -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.OpenRange.Constructions

noncomputable section

/-! The actual affine normalization source contains precisely the smooth-normalization points above its ambient open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.PrincipalBoundary.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GenericFibers.Constructions.Open

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (B : V.carrier.Opens) (hB : B ≤ Normalization.AmbientMap.Constructions.ambientOpen V D.val)

theorem sourceToSmooth_mem_range (y : (Normalization.AmbientMap.Constructions.smoothNormalizationOver V D.val).left) :
    y ∈ Set.range (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB).left ↔ (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V D.val).left y ∈ B := by
  rw [Normalization.GoodSmoothMap.Constructions.Range.fullAmbientMap_apply D y]
  constructor
  · rintro ⟨x, rfl⟩
    have he := (Normalization.Scheme.Constructions.normalization D.scheme).homOfLE_apply (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource_le_smooth D B hB) x
    exact (congrArg (fun z => D.inclusion (Normalization.Scheme.Constructions.normalizationMap D.scheme z)) he).symm ▸ x.property
  · intro hy
    let x : (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource D B).left := ⟨y.val, hy⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact (Normalization.Scheme.Constructions.normalization D.scheme).homOfLE_apply (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineSource_le_smooth D B hB) x

theorem sourceToSmooth_range : Set.range (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB).left =
    (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V D.val).left ⁻¹' (B : Set V.carrier) := by
  ext y
  exact sourceToSmooth_mem_range D B hB y

theorem sourceToSmooth_analytic_range : Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB)) =
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V D.val) ⁻¹'
      (ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen V.toOver B : Set V.analyticSpace) := by
  rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion, sourceToSmooth_range]
  rfl

omit hB in
theorem baseInclusion_analytic_range : Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)) =
    (ProperImage.AnalyticRestriction.Constructions.Construction.schemeAnalyticOpen V.toOver B : Set V.analyticSpace) := by
  rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion]
  change (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying : V.analyticSpace → V.carrier) ⁻¹'
    Set.range (B.ι : (B : Scheme) ⟶ V.carrier) = _
  rw [Scheme.Opens.range_ι]
  rfl

theorem affine_source_cover (U : Opens V.analyticSpace)
    (hU : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B))) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V D.val) ⁻¹' (U : Set V.analyticSpace) ⊆
      Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB)) := by
  rw [sourceToSmooth_analytic_range]
  intro x hx
  exact (Set.ext_iff.mp (baseInclusion_analytic_range B) _).mp (hU hx)

theorem affine_openBase_eq : Normalization.GenericFibers.Constructions.Open.openBase D (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB) =
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) ∘ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineMap D B) := by
  funext x
  exact (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth D B hB) (Normalization.PrincipalBoundary.Constructions.fullAmbientMap V D.val) x).symm.trans
    ((congrArg (fun f => ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f x) (Normalization.GoodSmoothMap.Constructions.AffineOpen.sourceToSmooth_ambient D B hB)).trans
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp (Normalization.GoodSmoothMap.Constructions.AffineOpen.affineMap D B) (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) x))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.OpenRange.Constructions
