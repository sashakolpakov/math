import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportCodimension
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportOverIso

/-! # Product Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions

noncomputable section

/-! The genuine product support in the integral-variety cycle grading,
with the presentation/component grading identified by actual open immersions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportCodimension.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) : LocallyOfFiniteType X.toOver.hom :=
  inferInstanceAs (LocallyOfFiniteType X.structureMap)

theorem integralPresentation_supportCodimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (A : IrreducibleCloseds V.carrier) : V.presentation.supportCodimension A = Geometric.DimensionCycles.dimensionCodimension V A := by
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion
    (V.presentation.componentInclusion (V.presentation.supportComponent A)) V.structureMap
  rw [V.presentation.componentInclusion_over] at h
  unfold Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.supportCodimension Geometric.DimensionCycles.dimensionCodimension
  rw [h]

variable (V W T : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (πV : T.toOver ⟶ V.toOver) (πW : T.toOver ⟶ W.toOver)
  (hprod : IsLimit (BinaryFan.mk πV πW)) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport W q)

def integralProductSupport : Geometric.DimensionCycles.DimensionCycleSupport T (p + q) :=
  ⟨Product.SupportScheme.Constructions.productIrreducibleSupport V.toOver W.toOver A.val B.val T.toOver πV πW hprod, by
    rw [← integralPresentation_supportCodimension T,
      Product.SupportCodimension.Constructions.productIrreducibleSupport_codimension V.presentation W.presentation T.presentation πV πW hprod,
      integralPresentation_supportCodimension V, integralPresentation_supportCodimension W]
    exact congrArg₂ (· + ·) A.property B.property⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions
