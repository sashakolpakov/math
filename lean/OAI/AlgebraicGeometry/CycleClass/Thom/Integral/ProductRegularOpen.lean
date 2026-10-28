import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductPointRanges
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExcision

/-! # Product Regular Open -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductRegularOpen.Constructions

noncomputable section

/-! The actual product of the factor regular ambient neighborhoods, written
as an open neighborhood of the entire regular product support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExcision.Cycles

open OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductPointRanges.Constructions.RegularPoints OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductPointRanges.Constructions
  Product.PresentationPoints.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V W T : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (πV : T.toOver ⟶ V.toOver) (πW : T.toOver ⟶ W.toOver)
  (hprod : IsLimit (BinaryFan.mk πV πW)) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport W q)

local notation "C" => OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions.integralProductSupport V W T πV πW hprod p q A B
local notation "e" => OAI.AlgebraicGeometry.CycleClass.Thom.Product.PresentationPoints.Constructions.productPresentationPointsHomeomorph V.toOver W.toOver T.toOver πV πW hprod

def integralProductRegularOpen : Opens (C).regularAmbientSpace :=
  ⟨{z | ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πV z.val ∈ A.regularAmbientOpen ∧
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πW z.val ∈ B.regularAmbientOpen},
    (A.regularAmbientOpen.isOpen.preimage
      ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map πV).comp continuous_subtype_val)).inter
    (B.regularAmbientOpen.isOpen.preimage
      ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map πW).comp continuous_subtype_val))⟩

local notation "U" => OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductRegularOpen.Constructions.integralProductRegularOpen V W T πV πW hprod p q A B

theorem integralProductRegularOpen_contains (z : (C).regularAnalyticSpace) :
    (C).regularComplementInclusion z ∈ U := by
  constructor
  · change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πV ((C).regularAnalyticToAmbient z) ∈ A.regularAmbientOpen
    rw [← ProductPointRanges.Constructions.RegularPoints.integralProductRegularHomeomorph_fst V W T πV πW hprod p q A B z]
    exact A.regularAnalyticToAmbient_not_mem_boundary _
  · change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πW ((C).regularAnalyticToAmbient z) ∈ B.regularAmbientOpen
    rw [← ProductPointRanges.Constructions.RegularPoints.integralProductRegularHomeomorph_snd V W T πV πW hprod p q A B z]
    exact B.regularAnalyticToAmbient_not_mem_boundary _

def integralProductOpenInclusion : (C).regularAnalyticSpace → U :=
  fun z => ⟨(C).regularComplementInclusion z,
    integralProductRegularOpen_contains V W T πV πW hprod p q A B z⟩

theorem integralProductOpenInclusion_closed : Topology.IsClosedEmbedding
    (integralProductOpenInclusion V W T πV πW hprod p q A B) := by
  refine ⟨(C).isClosedEmbedding_regularComplementInclusion.isEmbedding.codRestrict _ _, ?_⟩
  exact ((C).isClosedEmbedding_regularComplementInclusion.isClosedMap.codRestrict
    (integralProductRegularOpen_contains V W T πV πW hprod p q A B)).isClosed_range

def integralProductRegularOpenHomeomorph : U ≃ₜ (A.regularAmbientSpace × B.regularAmbientSpace) where
  toFun z := (⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πV z.val.val, z.property.1⟩,
    ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πW z.val.val, z.property.2⟩)
  invFun xy := by
    let z := (e).symm (xy.1.val, xy.2.val)
    have ha : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πV z ∈ A.regularAmbientOpen := by
      have h := congrArg Prod.fst ((e).apply_symm_apply (xy.1.val, xy.2.val))
      change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πV z = xy.1.val at h
      rw [h]
      exact xy.1.property
    have hb : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πW z ∈ B.regularAmbientOpen := by
      have h := congrArg Prod.snd ((e).apply_symm_apply (xy.1.val, xy.2.val))
      change ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map πW z = xy.2.val at h
      rw [h]
      exact xy.2.property
    exact ⟨⟨z, ProductPointRanges.Constructions.integralProduct_regularAmbient_contains V W T πV πW hprod p q A B z ha hb⟩, ha, hb⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact (e).symm_apply_apply z.val.val
  right_inv xy := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst ((e).apply_symm_apply (xy.1.val, xy.2.val))
    · apply Subtype.ext
      exact congrArg Prod.snd ((e).apply_symm_apply (xy.1.val, xy.2.val))
  continuous_toFun :=
    (((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map πV).comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).prodMk
    (((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map πW).comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)
  continuous_invFun :=
    (((e).symm.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _).subtype_mk _

theorem integralProductRegularOpenHomeomorph_inclusion (z : (C).regularAnalyticSpace) :
    integralProductRegularOpenHomeomorph V W T πV πW hprod p q A B
      (integralProductOpenInclusion V W T πV πW hprod p q A B z) =
    Prod.map A.regularComplementInclusion B.regularComplementInclusion
      (ProductPointRanges.Constructions.RegularPoints.integralProductRegularHomeomorph V W T πV πW hprod p q A B z) := by
  apply Prod.ext
  · apply Subtype.ext
    exact (ProductPointRanges.Constructions.RegularPoints.integralProductRegularHomeomorph_fst V W T πV πW hprod p q A B z).symm
  · apply Subtype.ext
    exact (ProductPointRanges.Constructions.RegularPoints.integralProductRegularHomeomorph_snd V W T πV πW hprod p q A B z).symm

theorem integralProductRegularOpen_excision (n : ℕ) :
    IsIso (Geometric.RelativeCohomologyExcision.Cycles.closedSupportCohomologyRestriction (TopCat.of (C).regularAmbientSpace)
      (U : Set (C).regularAmbientSpace) (Set.range (C).regularComplementInclusion) n) :=
  Geometric.RelativeCohomologyExcision.Cycles.closedSupportCohomologyRestriction_isIso (TopCat.of (C).regularAmbientSpace)
    (U : Set (C).regularAmbientSpace) (Set.range (C).regularComplementInclusion)
    (C).isClosedEmbedding_regularComplementInclusion.isClosed_range (U).isOpen
    (by rintro _ ⟨z, rfl⟩; exact integralProductRegularOpen_contains V W T πV πW hprod p q A B z) n

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductRegularOpen.Constructions
