import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductRegularOpen
import OAI.AlgebraicGeometry.CycleClass.Thom.AnalyticProductMaps
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.Immersion

/-! # Product Open Analytic -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductOpenAnalytic.Constructions

noncomputable section

/-! Holomorphicity of the actual product regular neighborhood comparison,
and the genuine immersion into this open neighborhood. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductPointRanges.Constructions.RegularPoints OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductRegularOpen.Constructions
  Product.PresentationPoints.Constructions AnalyticProductMaps.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : IsIntegral V.toOver.left := V.property
local instance (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : Smooth V.toOver.hom := V.presentation.smooth

variable (V W T : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (πV : T.toOver ⟶ V.toOver) (πW : T.toOver ⟶ W.toOver)
  (hprod : IsLimit (BinaryFan.mk πV πW)) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport W q)

local instance (priority := low) : ChartedSpace (V.analyticModel × W.analyticModel)
    (A.regularAmbientSpace × B.regularAmbientSpace) :=
  Product.Immersion.Constructions.productModelCharted _ _ _ _
local instance (priority := low) : ChartedSpace (V.analyticModel × W.analyticModel)
    (V.analyticSpace × W.analyticSpace) :=
  Product.Immersion.Constructions.productModelCharted _ _ _ _

local notation "C" => OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions.integralProductSupport V W T πV πW hprod p q A B
local notation "U" => OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductRegularOpen.Constructions.integralProductRegularOpen V W T πV πW hprod p q A B
local notation "e" => OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductRegularOpen.Constructions.integralProductRegularOpenHomeomorph V W T πV πW hprod p q A B
local notation "f" => OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductRegularOpen.Constructions.integralProductOpenInclusion V W T πV πW hprod p q A B

theorem integralProductOpenInclusion_contMDiff (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, (C).regularAnalyticModel) 𝓘(ℂ, T.analyticModel) r f := by
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff U f r).mp
  exact (C).contMDiff_regularComplementInclusion r

theorem integralProductOpenInclusion_mfderiv_injective (z : (C).regularAnalyticSpace) :
    Function.Injective (mfderiv 𝓘(ℂ, (C).regularAnalyticModel) 𝓘(ℂ, T.analyticModel) f z) := by
  exact (congrArg (fun l : (C).regularAnalyticModel →L[ℂ] T.analyticModel => Function.Injective l)
    (ComplexPoints.Analytic.RegularLocusComplement.mfderiv_intoOpen_eq U f z)).mpr ((C).mfderiv_regularComplementInclusion_injective z)

theorem integralProductRegularOpenHomeomorph_contMDiff (r : ℕ∞ω) :
    ContMDiff 𝓘(ℂ, T.analyticModel) (𝓘(ℂ, V.analyticModel).prod 𝓘(ℂ, W.analyticModel)) r e := by
  apply ContMDiff.prodMk
  · apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff A.regularAmbientOpen _ r).mp
    exact ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map πV r).comp
      (contMDiff_subtype_val («U» := (C).regularAmbientOpen) (n := r))).comp (contMDiff_subtype_val («U» := U) (n := r))
  · apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff B.regularAmbientOpen _ r).mp
    exact ((ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map πW r).comp
      (contMDiff_subtype_val («U» := (C).regularAmbientOpen) (n := r))).comp (contMDiff_subtype_val («U» := U) (n := r))

theorem integralProductRegularOpenHomeomorph_symm_contMDiff (r : ℕ∞ω) :
    ContMDiff (𝓘(ℂ, V.analyticModel).prod 𝓘(ℂ, W.analyticModel)) 𝓘(ℂ, T.analyticModel) r (e).symm := by
  rw [← modelWithCornersSelf_prod]
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff U (e).symm r).mp
  apply (ComplexPoints.Analytic.RegularLocusComplement.contMDiff_intoOpen_iff (C).regularAmbientOpen (Subtype.val ∘ (e).symm) r).mp
  rw [modelWithCornersSelf_prod]
  exact (AnalyticProductMaps.Constructions.productPresentationPointsHomeomorph_symm_contMDiff πV πW hprod r).comp
    ((contMDiff_subtype_val («U» := A.regularAmbientOpen) (n := r)).prodMap
      (contMDiff_subtype_val («U» := B.regularAmbientOpen) (n := r)))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductOpenAnalytic.Constructions
