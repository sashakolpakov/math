import OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProduct
import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.GradedProductSupport

/-! # Component Product Supports -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProductSupports.Constructions

noncomputable section

/-! The reduced product support computed in a native integral component
has exactly the prescribed ambient product support and codimension. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProduct.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProduct.Constructions.Projections OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions
  Product.SupportScheme.Constructions GradedProductSupport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : LocallyOfFiniteType V.toOver.hom :=
  inferInstanceAs (LocallyOfFiniteType V.structureMap)
local instance (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) : LocallyOfFiniteType X.toOver.hom :=
  inferInstanceAs (LocallyOfFiniteType X.structureMap)

variable (X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (C : irreducibleComponents X.carrier) (D : irreducibleComponents Y.carrier)
  (Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
  (hprod : IsLimit (BinaryFan.mk πX πY)) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport (X.componentVariety C) p) (B : Geometric.DimensionCycles.DimensionCycleSupport (Y.componentVariety D) q)

local notation "E" => OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProduct.Constructions.productComponent X Y C D Z πX πY hprod
local notation "v" => OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProduct.Constructions.Projections.productComponentFst X Y C D Z πX πY hprod
local notation "w" => OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProduct.Constructions.Projections.productComponentSnd X Y C D Z πX πY hprod
local notation "hp" => OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProduct.Constructions.Projections.productComponentIsLimit X Y C D Z πX πY hprod
local notation "S" => OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions.integralProductSupport (X.componentVariety C) (Y.componentVariety D)
  (Z.componentVariety E) v w hp p q A B

theorem componentProductSupport_image : Z.componentSupportImage E (S).val =
    Product.SupportScheme.Constructions.productIrreducibleSupport X.toOver Y.toOver (X.componentSupportImage C A.val)
      (Y.componentSupportImage D B.val) Z.toOver πX πY hprod := by
  have hx (t : (Z.componentVariety E).carrier) :
      X.componentInclusion C ((v).left t) = πX.left (Z.componentInclusion E t) :=
    congrArg (fun φ : (Z.componentVariety E).toOver ⟶ X.toOver => φ.left t)
      (ComponentProduct.Constructions.Projections.productComponentFst_inclusion X Y C D Z πX πY hprod)
  have hy (t : (Z.componentVariety E).carrier) :
      Y.componentInclusion D ((w).left t) = πY.left (Z.componentInclusion E t) :=
    congrArg (fun φ : (Z.componentVariety E).toOver ⟶ Y.toOver => φ.left t)
      (ComponentProduct.Constructions.Projections.productComponentSnd_inclusion X Y C D Z πX πY hprod)
  apply IrreducibleCloseds.ext
  rw [Z.componentSupportImage_coe]
  change Z.componentInclusion E ''
    (Product.SupportScheme.Constructions.productIrreducibleSupport (X.componentVariety C).toOver (Y.componentVariety D).toOver
      A.val B.val (Z.componentVariety E).toOver v w hp : Set (Z.componentVariety E).toOver.left) = _
  rw [Product.SupportScheme.Constructions.productIrreducibleSupport_coe, Product.SupportScheme.Constructions.productIrreducibleSupport_coe,
    X.componentSupportImage_coe, Y.componentSupportImage_coe]
  ext z
  constructor
  · rintro ⟨t, ⟨htA, htB⟩, rfl⟩
    exact ⟨⟨(v).left t, htA, hx t⟩, ⟨(w).left t, htB, hy t⟩⟩
  · rintro ⟨⟨a, ha, haz⟩, ⟨b, hb, hbz⟩⟩
    have hzE : z ∈ (E).val := by
      rw [ComponentProduct.Constructions.productComponent_range]
      constructor
      · rw [← X.componentInclusion_range C]
        exact ⟨a, haz⟩
      · rw [← Y.componentInclusion_range D]
        exact ⟨b, hbz⟩
    rw [← Z.componentInclusion_range E] at hzE
    obtain ⟨t, rfl⟩ := hzE
    refine ⟨t, ⟨?_, ?_⟩, rfl⟩
    · have ht : (v).left t = a := (X.componentInclusion C).isOpenEmbedding.injective ((hx t).trans haz.symm)
      change (v).left t ∈ (A.val : Set (X.componentVariety C).carrier)
      exact ht.symm ▸ ha
    · have ht : (w).left t = b := (Y.componentInclusion D).isOpenEmbedding.injective ((hy t).trans hbz.symm)
      change (w).left t ∈ (B.val : Set (Y.componentVariety D).carrier)
      exact ht.symm ▸ hb

theorem componentProductDimensionSupport :
    GradedProductSupport.Constructions.productDimensionSupport X Y Z πX πY hprod p q
      ((X.componentDimensionSupportEquiv p).symm ⟨C, A⟩)
      ((Y.componentDimensionSupportEquiv q).symm ⟨D, B⟩) =
    (Z.componentDimensionSupportEquiv (p + q)).symm ⟨E, S⟩ := by
  apply Subtype.ext
  rw [Z.componentDimensionSupportEquiv_symm_val]
  exact (componentProductSupport_image X Y C D Z πX πY hprod p q A B).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ComponentProductSupports.Constructions
