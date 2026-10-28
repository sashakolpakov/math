import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportTo
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ComponentDimension

/-! # Support Codimension -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportCodimension.Constructions

noncomputable section

/-! Codimensions of genuine reduced product supports add, with dimensions
measured in the actual containing components even for disconnected schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.Dimension OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportTo.Constructions.PresentationMap
  Open.ComponentDimension.Constructions Scheme.ProductDimension.Constructions Scheme.ProductIntegral.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) : LocallyOfFiniteType X.toOver.hom :=
  inferInstanceAs (LocallyOfFiniteType X.structureMap)

local instance (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : IsIntegral V.toOver.left :=
  inferInstanceAs (IsIntegral V.carrier)

theorem support_dimension_le_component (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A : IrreducibleCloseds X.carrier) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension A X.structureMap ≤
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (X.componentVariety (X.supportComponent A)).structureMap := by
  let C := X.supportComponent A
  let W := X.componentSupportPreimage C A (X.support_subset_component A)
  have h := X.componentSupportImage_transcendenceDimension C W
  have he : X.componentSupportImage C W = A := X.componentSupportImage_preimage C A _
  rw [he] at h
  exact h.trans_le (Foundations.Scheme.SupportDimension.supportTranscendenceDimension_le W (X.componentVariety C).structureMap)

variable (X Y Z : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (πX : Z.toOver ⟶ X.toOver) (πY : Z.toOver ⟶ Y.toOver)
  (hprod : IsLimit (BinaryFan.mk πX πY))
  (A : IrreducibleCloseds X.carrier) (B : IrreducibleCloseds Y.carrier)

theorem product_support_component_dimension :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Z.componentVariety (Z.supportComponent
      (SupportScheme.Constructions.productIrreducibleSupport X.toOver Y.toOver A B Z.toOver πX πY hprod))).structureMap =
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (X.componentVariety (X.supportComponent A)).structureMap +
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Y.componentVariety (Y.supportComponent B)).structureMap := by
  let C := X.supportComponent A
  let D := Y.supportComponent B
  let U := (X.componentVariety C).toOver
  let V := (Y.componentVariety D).toOver
  let i : U ⟶ X.toOver := Over.homMk (X.componentInclusion C) (X.componentInclusion_over C)
  let j : V ⟶ Y.toOver := Over.homMk (Y.componentInclusion D) (Y.componentInclusion_over D)
  let : IsIntegral U.left := inferInstanceAs (IsIntegral (X.componentVariety C).carrier)
  let : IsIntegral V.left := inferInstanceAs (IsIntegral (Y.componentVariety D).carrier)
  let : LocallyOfFiniteType U.hom := inferInstanceAs (LocallyOfFiniteType (X.componentVariety C).structureMap)
  let : LocallyOfFiniteType V.hom := inferInstanceAs (LocallyOfFiniteType (Y.componentVariety D).structureMap)
  let : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion (X.componentInclusion C))
  let : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (Y.componentInclusion D))
  let := Scheme.ProductIntegral.Constructions.schemeProduct_isIntegral U V
  let m := SupportTo.Constructions.PresentationMap.productPresentationMap X.toOver Y.toOver Z.toOver πX πY hprod U V i j
  have hS : (SupportScheme.Constructions.productIrreducibleSupport X.toOver Y.toOver A B Z.toOver πX πY hprod : Set Z.toOver.left) ⊆
      Set.range m := by
    rw [SupportScheme.Constructions.productIrreducibleSupport_coe, SupportTo.Constructions.PresentationMap.productPresentationMap_range]
    change πX.left ⁻¹' (A : Set X.carrier) ∩ πY.left ⁻¹' (B : Set Y.carrier) ⊆
      πX.left ⁻¹' Set.range (X.componentInclusion C) ∩ πY.left ⁻¹' Set.range (Y.componentInclusion D)
    rw [X.componentInclusion_range C, Y.componentInclusion_range D]
    exact Set.inter_subset_inter (Set.preimage_mono (X.support_subset_component A))
      (Set.preimage_mono (Y.support_subset_component B))
  have h := Open.ComponentDimension.Constructions.component_dimension_of_open_integral_neighborhood Z
    (SupportScheme.Constructions.productIrreducibleSupport X.toOver Y.toOver A B Z.toOver πX πY hprod) m hS
  have hb : m ≫ Z.structureMap = pullback.fst U.hom V.hom ≫ U.hom :=
    SupportTo.Constructions.PresentationMap.productPresentationMap_base X.toOver Y.toOver Z.toOver πX πY hprod U V i j
  rw [hb] at h
  exact h.trans (Scheme.ProductDimension.Constructions.schemeProduct_dimension U V)

theorem productIrreducibleSupport_codimension :
    Z.supportCodimension (SupportScheme.Constructions.productIrreducibleSupport X.toOver Y.toOver A B Z.toOver πX πY hprod) =
      X.supportCodimension A + Y.supportCodimension B := by
  unfold Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.supportCodimension
  rw [product_support_component_dimension X Y Z πX πY hprod A B]
  have hd := SupportTo.Constructions.Dimension.productIrreducibleSupport_dimension X.toOver Y.toOver A B Z.toOver πX πY hprod
  change Foundations.Scheme.SupportDimension.supportTranscendenceDimension
    (SupportScheme.Constructions.productIrreducibleSupport X.toOver Y.toOver A B Z.toOver πX πY hprod) Z.structureMap =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension A X.structureMap + Foundations.Scheme.SupportDimension.supportTranscendenceDimension B Y.structureMap at hd
  rw [hd]
  have ha := support_dimension_le_component X A
  have hb := support_dimension_le_component Y B
  omega

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportCodimension.Constructions
