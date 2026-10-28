import OAI.AlgebraicGeometry.CycleClass.Thom.ComponentRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProductSupports
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.ComponentEquiv
import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.Product

/-! # Exterior -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.Exterior.Constructions.Supports

/-! Exterior compatibility on genuine unit supports, assembled from the
actual integral-component product formula and the native component restrictions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Betti.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ComponentRestriction.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProduct.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProduct.Constructions.Projections
  ComponentProductSupports.Constructions Product.ComponentEquiv.Constructions Integral.ProductSupport.Constructions
  Integral.Product.Constructions GradedProductSupport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (C : irreducibleComponents X.carrier) (D : irreducibleComponents Y.carrier)
  (Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
  (hprod : IsLimit (BinaryFan.mk πX πY)) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport (X.componentVariety C) p) (B : Geometric.DimensionCycles.DimensionCycleSupport (Y.componentVariety D) q)

local notation "AX" => Equiv.symm (X.componentDimensionSupportEquiv p) (Sigma.mk C A)
local notation "BY" => Equiv.symm (Y.componentDimensionSupportEquiv q) (Sigma.mk D B)
local notation "E" => OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProduct.Constructions.productComponent X Y C D Z πX πY hprod
local notation "v" => OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProduct.Constructions.Projections.productComponentFst X Y C D Z πX πY hprod
local notation "w" => OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProduct.Constructions.Projections.productComponentSnd X Y C D Z πX πY hprod
local notation "hp" => OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProduct.Constructions.Projections.productComponentIsLimit X Y C D Z πX πY hprod
local notation "S" => OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions.integralProductSupport (X.componentVariety C) (Y.componentVariety D)
  (Z.componentVariety E) v w hp p q A B

theorem exteriorSingleSupport_components :
    Z.geometricCycleClassMap (p + q)
      (Finsupp.single (GradedProductSupport.Constructions.productDimensionSupport X Y Z πX πY hprod p q AX BY) 1) =
    Betti.Constructions.exteriorBettiBilinear X Y Z πX πY p q
      (X.geometricCycleClassMap p (Finsupp.single AX 1))
      (Y.geometricCycleClassMap q (Finsupp.single BY 1)) := by
  rw [ComponentProductSupports.Constructions.componentProductDimensionSupport]
  apply Z.componentBetti_ext (ModuleCat.of ℚ ℚ) ((p + q) + (p + q))
  intro F
  obtain ⟨⟨C', D'⟩, rfl⟩ := Product.ComponentEquiv.Constructions.productComponent_surjective X Y Z πX πY hprod F
  rw [ComponentRestriction.Constructions.Class.exteriorBettiBilinear_restrict_components]
  by_cases hc : C = C'
  · subst C'
    by_cases hd : D = D'
    · subst D'
      rw [ComponentRestriction.Constructions.Class.geometricClass_single_component_same, ComponentRestriction.Constructions.Class.geometricClass_single_component_same,
        ComponentRestriction.Constructions.Class.geometricClass_single_component_same, one_smul, one_smul, one_smul, Betti.Constructions.exteriorBettiBilinear_apply]
      exact Integral.Product.Constructions.integralGeometricCycleClass_product (X.componentVariety C) (Y.componentVariety D)
        (Z.componentVariety E) v w hp p q A B
    · have he : E ≠ ComponentProduct.Constructions.productComponent X Y C D' Z πX πY hprod := by
        intro h
        exact hd (congrArg Prod.snd (@Product.ComponentEquiv.Constructions.productComponent_injective X Y Z πX πY hprod (C, D) (C, D') h))
      rw [ComponentRestriction.Constructions.Class.geometricClass_single_component_ne Z (p + q) E _ S 1 he,
        ComponentRestriction.Constructions.Class.geometricClass_single_component_ne Y q D D' B 1 hd, map_zero]
  · have he : E ≠ ComponentProduct.Constructions.productComponent X Y C' D' Z πX πY hprod := by
      intro h
      exact hc (congrArg Prod.fst (@Product.ComponentEquiv.Constructions.productComponent_injective X Y Z πX πY hprod (C, D) (C', D') h))
    rw [ComponentRestriction.Constructions.Class.geometricClass_single_component_ne Z (p + q) E _ S 1 he,
      ComponentRestriction.Constructions.Class.geometricClass_single_component_ne X p C C' A 1 hc, map_zero, LinearMap.zero_apply]

end AlgebraicGeometry.CycleClass.Thom.Exterior.Constructions.Supports

namespace AlgebraicGeometry.CycleClass.Thom.Exterior

/-! ThomClass exterior compatibility for all actual rational cycles on arbitrary
smooth projective presentations, using the faithfully repaired cycle product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.CycleClass.Thom.Betti.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Exterior.Constructions.Supports OAI.AlgebraicGeometry.CycleClass.Thom.GradedProductSupport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Cycle classes take genuine reduced exterior products to the cup product
of the actual projection pullbacks. Empty and mixed-dimensional presentations
are included through their native component decompositions. -/
theorem cycle_class_exterior
    (X Y Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
    (hprod : IsLimit (BinaryFan.mk πX πY)) (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : Y.RationalDimensionCycle q) :
    Z.geometricCycleClassMap (p + q) (IntersectionGeometry.exteriorCycleProduct X Y Z πX πY hprod p q a b) =
      cast (congrArg (fun n => (Z.rationalCohomology n : Type)) (add_add_add_comm p p q q))
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace Z.toOver) (p + p) (q + q)
          (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + p) πX (X.geometricCycleClassMap p a))
          (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (q + q) πY (Y.geometricCycleClassMap q b))) := by
  rw [← Betti.Constructions.exteriorBettiBilinear_apply]
  apply (Betti.Constructions.exterior_compatibility_iff_supports X Y Z πX πY hprod p q).mpr _ a b
  intro A B
  obtain ⟨⟨C, A⟩, rfl⟩ := (X.componentDimensionSupportEquiv p).symm.surjective A
  obtain ⟨⟨D, B⟩, rfl⟩ := (Y.componentDimensionSupportEquiv q).symm.surjective B
  rw [GradedProductSupport.Constructions.reducedProductCycle_eq_single X Y Z πX πY hprod]
  exact Constructions.Supports.exteriorSingleSupport_components X Y C D Z πX πY hprod p q A B

end AlgebraicGeometry.CycleClass.Thom.Exterior

end

end OAI
