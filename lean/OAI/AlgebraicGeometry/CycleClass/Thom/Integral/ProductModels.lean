import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.ProductCoordinates
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.CycleStratumRealization

/-! # Product Models -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductModels.Constructions

noncomputable section

/-! Actual complex dimensions and norm-preserving coordinates for a product
cycle's native ambient and regular-locus models. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.Dimension OAI.AlgebraicGeometry.CycleClass.Thom.Finite.ProductCoordinates.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : LocallyOfFiniteType V.toOver.hom :=
  inferInstanceAs (LocallyOfFiniteType V.structureMap)

def finiteProductCoordinatesOfEq (d c n : ℕ) (h : d + c = n) :
    ((Fin d → ℂ) × (Fin c → ℂ)) ≃L[ℂ] (Fin n → ℂ) :=
  h ▸ Finite.ProductCoordinates.Constructions.finiteProductCoordinates d c

theorem finiteProductCoordinatesOfEq_norm (d c n : ℕ) (h : d + c = n)
    (v : (Fin d → ℂ) × (Fin c → ℂ)) : ‖finiteProductCoordinatesOfEq d c n h v‖ = ‖v‖ := by
  subst n
  exact Finite.ProductCoordinates.Constructions.finiteProductCoordinates_norm d c v

variable (V W T : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (πV : T.toOver ⟶ V.toOver) (πW : T.toOver ⟶ W.toOver)
  (hprod : IsLimit (BinaryFan.mk πV πW)) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport W q)

local notation "C" => OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions.integralProductSupport V W T πV πW hprod p q A B

theorem integralProduct_regularComplexDimension :
    (C).regularComplexDimension = A.regularComplexDimension + B.regularComplexDimension := by
  rw [Geometric.DimensionCycles.DimensionCycleSupport.regularComplexDimension_eq_supportDimension,
    Geometric.DimensionCycles.DimensionCycleSupport.regularComplexDimension_eq_supportDimension,
    Geometric.DimensionCycles.DimensionCycleSupport.regularComplexDimension_eq_supportDimension]
  exact Product.SupportTo.Constructions.Dimension.productIrreducibleSupport_dimension V.toOver W.toOver A.val B.val T.toOver πV πW hprod

include hprod A B in
theorem integralProduct_complexDimension : T.complexDimension = V.complexDimension + W.complexDimension := by
  have h := integralProduct_regularComplexDimension V W T πV πW hprod p q A B
  have ha := A.regularComplexDimension_add_codimension
  have hb := B.regularComplexDimension_add_codimension
  have hc := (C).regularComplexDimension_add_codimension
  omega

def integralProductRegularModelCoordinates :
    (A.regularAnalyticModel × B.regularAnalyticModel) ≃L[ℂ] (C).regularAnalyticModel :=
  finiteProductCoordinatesOfEq A.regularComplexDimension B.regularComplexDimension
    (C).regularComplexDimension (integralProduct_regularComplexDimension V W T πV πW hprod p q A B).symm

theorem integralProductRegularModelCoordinates_norm (v : A.regularAnalyticModel × B.regularAnalyticModel) :
    ‖integralProductRegularModelCoordinates V W T πV πW hprod p q A B v‖ = ‖v‖ :=
  finiteProductCoordinatesOfEq_norm _ _ _ _ v

def integralProductAmbientModelCoordinates : (V.analyticModel × W.analyticModel) ≃L[ℂ] T.analyticModel :=
  finiteProductCoordinatesOfEq V.complexDimension W.complexDimension T.complexDimension
    (integralProduct_complexDimension V W T πV πW hprod p q A B).symm

theorem integralProductAmbientModelCoordinates_norm (v : V.analyticModel × W.analyticModel) :
    ‖integralProductAmbientModelCoordinates V W T πV πW hprod p q A B v‖ = ‖v‖ :=
  finiteProductCoordinatesOfEq_norm _ _ _ _ v

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductModels.Constructions
