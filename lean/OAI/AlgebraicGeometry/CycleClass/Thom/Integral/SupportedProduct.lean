import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductOpen
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProductRestriction
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedExcision

/-! # Supported Product -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Integral.SupportedProduct.Constructions

noncomputable section

/-! The genuine supported class of an integral product cycle is the pullback
of the exterior cup of the actual factor classes, including singular supports. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductRegularOpen.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductPointRanges.Constructions
  ProductOpen.Constructions Supported.ProductRestriction.Constructions Open.SupportedExcision.Constructions
  Product.PresentationPoints.Constructions NormalPair.TransportRestriction.Constructions Open.NormalPairRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V W T : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (πV : T.toOver ⟶ V.toOver) (πW : T.toOver ⟶ W.toOver)
  (hprod : IsLimit (BinaryFan.mk πV πW)) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport W q)

local notation "C" => OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions.integralProductSupport V W T πV πW hprod p q A B
local notation "U" => OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductRegularOpen.Constructions.integralProductRegularOpen V W T πV πW hprod p q A B
local notation "e" => OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductRegularOpen.Constructions.integralProductRegularOpenHomeomorph V W T πV πW hprod p q A B
local notation "f" => OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductRegularOpen.Constructions.integralProductOpenInclusion V W T πV πW hprod p q A B

def ambientProductMap : TopCat.of T.analyticSpace ⟶ TopCat.of (V.analyticSpace × W.analyticSpace) :=
  NormalPair.TransportRestriction.Constructions.ambientTransportMap (Product.PresentationPoints.Constructions.productPresentationPointsHomeomorph V.toOver W.toOver T.toOver πV πW hprod)

theorem ambientProductMap_mapsTo : Set.MapsTo (ambientProductMap V W T πV πW hprod)
    (Set.range (C).analyticInclusion)ᶜ (Set.range (Prod.map A.analyticInclusion B.analyticInclusion))ᶜ := by
  intro z hz hp
  apply hz
  rw [ProductPointRanges.Constructions.integralProductSupport_range]
  rw [Set.range_prodMap] at hp
  exact hp

def integralSupportedProductClass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of T.analyticSpace) (Set.range (C).analyticInclusion)ᶜ (2 * (p + q)) :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (ambientProductMap V W T πV πW hprod)
    (ambientProductMap_mapsTo V W T πV πW hprod p q A B) (2 * (p + q)) (Supported.ProductRestriction.Constructions.supportedExteriorCycleClass A B)

def productOpenToAmbient : TopCat.of U ⟶ TopCat.of T.analyticSpace :=
  Open.NormalPairRestriction.Constructions.openAmbientTransportMap Subtype.val (U).isOpenEmbedding' ≫
    Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of T.analyticSpace) (C).analyticSingularBoundaryᶜ

theorem productOpenToAmbient_mapsTo : Set.MapsTo (productOpenToAmbient V W T πV πW hprod p q A B)
    (Set.range f)ᶜ (Set.range (C).analyticInclusion)ᶜ :=
  (show Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of T.analyticSpace) (C).analyticSingularBoundaryᶜ)
    (Set.range (C).regularComplementInclusion)ᶜ (Set.range (C).analyticInclusion)ᶜ from
      fun x hx => ((C).mem_regularThomComplement_iff x).mp hx).comp
    (Open.NormalPairRestriction.Constructions.openAmbientTransportMapsTo f Subtype.val (U).isOpenEmbedding')

theorem productOpenToAmbient_square :
    productOpenToAmbient V W T πV πW hprod p q A B ≫ ambientProductMap V W T πV πW hprod =
      NormalPair.TransportRestriction.Constructions.ambientTransportMap e ≫ Supported.ProductRestriction.Constructions.regularProductAmbientMap A B := by
  ext z <;> rfl

theorem integralSupportedProductClass_openRestriction :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (productOpenToAmbient V W T πV πW hprod p q A B)
      (productOpenToAmbient_mapsTo V W T πV πW hprod p q A B) (2 * (p + q))
      (integralSupportedProductClass V W T πV πW hprod p q A B) =
      ProductOpen.Constructions.integralProductOpenThomClass V W T πV πW hprod p q A B := by
  have h₁ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (productOpenToAmbient V W T πV πW hprod p q A B) (ambientProductMap V W T πV πW hprod)
    (productOpenToAmbient_mapsTo V W T πV πW hprod p q A B)
    (ambientProductMap_mapsTo V W T πV πW hprod p q A B) (2 * (p + q))
  have h₂ := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (NormalPair.TransportRestriction.Constructions.ambientTransportMap e) (Supported.ProductRestriction.Constructions.regularProductAmbientMap A B)
    (ProductOpen.Constructions.integralProductOpen_mapsTo V W T πV πW hprod p q A B)
    (Supported.ProductRestriction.Constructions.regularProductAmbientMap_mapsTo A B) (2 * (p + q))
  simp only [productOpenToAmbient_square] at h₁
  have h := ConcreteCategory.congr_hom (h₁.trans h₂.symm) (Supported.ProductRestriction.Constructions.supportedExteriorCycleClass A B)
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (productOpenToAmbient V W T πV πW hprod p q A B)
    (productOpenToAmbient_mapsTo V W T πV πW hprod p q A B) (2 * (p + q))
    (integralSupportedProductClass V W T πV πW hprod p q A B) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPair.TransportRestriction.Constructions.ambientTransportMap e)
      (ProductOpen.Constructions.integralProductOpen_mapsTo V W T πV πW hprod p q A B) (2 * (p + q))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (Supported.ProductRestriction.Constructions.regularProductAmbientMap A B)
        (Supported.ProductRestriction.Constructions.regularProductAmbientMap_mapsTo A B) (2 * (p + q)) (Supported.ProductRestriction.Constructions.supportedExteriorCycleClass A B)) at h
  rw [Supported.ProductRestriction.Constructions.supportedExteriorCycleClass_regularRestriction, ProductOpen.Constructions.integralProductThom_pullback] at h
  exact h

theorem integralSupportedProductClass_eq_cycleClass :
    integralSupportedProductClass V W T πV πW hprod p q A B = (C).rationalSupportedCycleClass := by
  apply (C).rationalSupportedCycleClass_unique
  change (Geometric.RelativeCochainTriple.Cohomology.relativeCohomologyTripleRestriction (ModuleCat.of ℚ ℚ) (TopCat.of T.analyticSpace)
    (C).analyticSingularBoundaryᶜ (Set.range (C).analyticInclusion)ᶜ (2 * (p + q)) ≫
      ((C).regularThomCohomologyIso (ModuleCat.of ℚ ℚ) (2 * (p + q))).inv)
        (integralSupportedProductClass V W T πV πW hprod p q A B) = (C).regularThomClass
  rw [Geometric.DimensionCycles.DimensionCycleSupport.relativeCohomologyTripleRestriction_regularThom]
  apply Open.SupportedExcision.Constructions.openSupportedRestriction_injective U f (C).isClosedEmbedding_regularComplementInclusion.isClosed_range
    (2 * (p + q))
  have hm := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
    (Open.NormalPairRestriction.Constructions.openAmbientTransportMap Subtype.val (U).isOpenEmbedding')
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of T.analyticSpace) (C).analyticSingularBoundaryᶜ)
    (Open.NormalPairRestriction.Constructions.openAmbientTransportMapsTo f Subtype.val (U).isOpenEmbedding')
    (show Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of T.analyticSpace) (C).analyticSingularBoundaryᶜ)
      (Set.range (C).regularComplementInclusion)ᶜ (Set.range (C).analyticInclusion)ᶜ from
        fun x hx => ((C).mem_regularThomComplement_iff x).mp hx) (2 * (p + q))
  have h := ConcreteCategory.congr_hom hm (integralSupportedProductClass V W T πV πW hprod p q A B)
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (Open.NormalPairRestriction.Constructions.openAmbientTransportMap Subtype.val (U).isOpenEmbedding')
    (Open.NormalPairRestriction.Constructions.openAmbientTransportMapsTo f Subtype.val (U).isOpenEmbedding') (2 * (p + q))
    ((C).regularThomCohomologyRestriction (ModuleCat.of ℚ ℚ) (2 * (p + q))
      (integralSupportedProductClass V W T πV πW hprod p q A B)) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (productOpenToAmbient V W T πV πW hprod p q A B)
      (productOpenToAmbient_mapsTo V W T πV πW hprod p q A B) (2 * (p + q))
      (integralSupportedProductClass V W T πV πW hprod p q A B) at h
  rw [integralSupportedProductClass_openRestriction] at h
  exact h.trans (ProductOpen.Constructions.integralProductOpenThom_restriction V W T πV πW hprod p q A B).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Integral.SupportedProduct.Constructions
