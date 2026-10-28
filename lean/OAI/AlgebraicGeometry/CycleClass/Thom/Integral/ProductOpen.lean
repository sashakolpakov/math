import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductOpenAnalytic
import OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductModels
import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.Product
import OAI.AlgebraicGeometry.CycleClass.Thom.CommutingSquare
import OAI.AlgebraicGeometry.CycleClass.Thom.OpenNaturality

/-! # Product Open -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductOpen.Constructions

noncomputable section

/-! The actual product regular-locus Thom class pulls back to the native
Thom class in the open product neighborhood of the genuine product cycle. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductPointRanges.Constructions.RegularPoints OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductRegularOpen.Constructions
  ProductOpenAnalytic.Constructions ProductModels.Constructions Product.Immersion.Constructions Regular.Product.Constructions
  Degree.Constructions.ThomClass CommutingSquare.Constructions NormalPair.TransportRestriction.Constructions
  OpenNaturality.Constructions Open.NormalPairRestriction.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V W T : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (πV : T.toOver ⟶ V.toOver) (πW : T.toOver ⟶ W.toOver)
  (hprod : IsLimit (BinaryFan.mk πV πW)) (p q : ℕ)
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport W q)

local notation "C" => OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductSupport.Constructions.integralProductSupport V W T πV πW hprod p q A B
local notation "U" => OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductRegularOpen.Constructions.integralProductRegularOpen V W T πV πW hprod p q A B
local notation "e" => OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductRegularOpen.Constructions.integralProductRegularOpenHomeomorph V W T πV πW hprod p q A B
local notation "f" => OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductRegularOpen.Constructions.integralProductOpenInclusion V W T πV πW hprod p q A B
local notation "g" => Prod.map A.regularComplementInclusion B.regularComplementInclusion
local notation "r" => OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductPointRanges.Constructions.RegularPoints.integralProductRegularHomeomorph V W T πV πW hprod p q A B

local instance (priority := low) : ChartedSpace (A.regularAnalyticModel × B.regularAnalyticModel)
    (A.regularAnalyticSpace × B.regularAnalyticSpace) := Product.Immersion.Constructions.productModelCharted _ _ _ _
local instance (priority := low) : ChartedSpace (V.analyticModel × W.analyticModel)
    (A.regularAmbientSpace × B.regularAmbientSpace) := Product.Immersion.Constructions.productModelCharted _ _ _ _
local instance : IsManifold 𝓘(ℂ, A.regularAnalyticModel × B.regularAnalyticModel) ω
    (A.regularAnalyticSpace × B.regularAnalyticSpace) := Product.Immersion.Constructions.productModel_isManifold
local instance : IsManifold 𝓘(ℂ, V.analyticModel × W.analyticModel) ω
    (A.regularAmbientSpace × B.regularAmbientSpace) := Product.Immersion.Constructions.productModel_isManifold
local instance : MetrizableSpace U := (U).isOpenEmbedding'.isEmbedding.metrizableSpace

theorem integralProductOpen_commutes : e ∘ f = g ∘ r :=
  funext (ProductRegularOpen.Constructions.integralProductRegularOpenHomeomorph_inclusion V W T πV πW hprod p q A B)

theorem integralProductOpen_productCodimension :
    Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension (C).regularAnalyticModel (V.analyticModel × W.analyticModel) = p + q := by
  have hc := (C).regularComplexDimension_add_codimension
  have ht := ProductModels.Constructions.integralProduct_complexDimension V W T πV πW hprod p q A B
  rw [Geometric.ComplexNormalAtlas.Cycles.complexImmersionCodimension, Module.finrank_prod, V.analyticModel_complex_finrank,
    W.analyticModel_complex_finrank]
  change V.complexDimension + W.complexDimension - Module.finrank ℂ (Fin (C).regularComplexDimension → ℂ) = _
  rw [Module.finrank_pi, Fintype.card_fin]
  omega

def integralProductOpenThomClass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of U) (Set.range f)ᶜ (2 * (p + q)) :=
  Degree.Constructions.ThomClass.complexThomClassInDegree f
    (ProductOpenAnalytic.Constructions.integralProductOpenInclusion_contMDiff V W T πV πW hprod p q A B ω)
    (ProductOpenAnalytic.Constructions.integralProductOpenInclusion_mfderiv_injective V W T πV πW hprod p q A B)
    (ProductRegularOpen.Constructions.integralProductOpenInclusion_closed V W T πV πW hprod p q A B)
    (p + q) (C).regularComplement_complexImmersionCodimension

theorem integralProductOpen_mapsTo : Set.MapsTo (NormalPair.TransportRestriction.Constructions.ambientTransportMap e)
    (Set.range f)ᶜ (Set.range g)ᶜ :=
  CommutingSquare.Constructions.squareMapsTo f g e r (r).surjective (integralProductOpen_commutes V W T πV πW hprod p q A B)

theorem integralProductThom_pullback :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalPair.TransportRestriction.Constructions.ambientTransportMap e)
      (integralProductOpen_mapsTo V W T πV πW hprod p q A B) (2 * (p + q))
      (Regular.Product.Constructions.regularProductThomClass A B) = integralProductOpenThomClass V W T πV πW hprod p q A B := by
  have he : ContMDiff 𝓘(ℂ, T.analyticModel) 𝓘(ℂ, V.analyticModel × W.analyticModel) ω e := by
    rw [modelWithCornersSelf_prod]
    exact ProductOpenAnalytic.Constructions.integralProductRegularOpenHomeomorph_contMDiff V W T πV πW hprod p q A B ω
  have hei : MDifferentiable 𝓘(ℂ, V.analyticModel × W.analyticModel) 𝓘(ℂ, T.analyticModel) (e).symm := by
    rw [modelWithCornersSelf_prod]
    exact (ProductOpenAnalytic.Constructions.integralProductRegularOpenHomeomorph_symm_contMDiff V W T πV πW hprod p q A B ω).mdifferentiable (by simp)
  exact CommutingSquare.Constructions.complexThomClassInDegree_commutingSquare f
    (ProductOpenAnalytic.Constructions.integralProductOpenInclusion_contMDiff V W T πV πW hprod p q A B ω)
    (ProductOpenAnalytic.Constructions.integralProductOpenInclusion_mfderiv_injective V W T πV πW hprod p q A B)
    (ProductRegularOpen.Constructions.integralProductOpenInclusion_closed V W T πV πW hprod p q A B)
    g (Product.Immersion.Constructions.productImmersion_contMDiff A.regularComplementInclusion B.regularComplementInclusion
      (A.contMDiff_regularComplementInclusion ω) (B.contMDiff_regularComplementInclusion ω))
    (Product.Immersion.Constructions.productImmersion_injective_mfderiv A.regularComplementInclusion B.regularComplementInclusion
      (A.contMDiff_regularComplementInclusion ω) (B.contMDiff_regularComplementInclusion ω)
      A.mfderiv_regularComplementInclusion_injective B.mfderiv_regularComplementInclusion_injective)
    (A.isClosedEmbedding_regularComplementInclusion.prodMap B.isClosedEmbedding_regularComplementInclusion)
    e he hei r (r).surjective (integralProductOpen_commutes V W T πV πW hprod p q A B)
    (ProductModels.Constructions.integralProductRegularModelCoordinates V W T πV πW hprod p q A B)
    (ProductModels.Constructions.integralProductRegularModelCoordinates_norm V W T πV πW hprod p q A B)
    (p + q) (C).regularComplement_complexImmersionCodimension
    ((Product.Immersion.Constructions.complexImmersionCodimension_prod (Regular.Product.Constructions.regular_model_finrank_le A) (Regular.Product.Constructions.regular_model_finrank_le B)).trans
      (congrArg₂ (· + ·) A.regularComplement_complexImmersionCodimension B.regularComplement_complexImmersionCodimension))
    (integralProductOpen_productCodimension V W T πV πW hprod p q A B)

theorem integralProductOpenThom_restriction :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Open.NormalPairRestriction.Constructions.openAmbientTransportMap Subtype.val (U).isOpenEmbedding')
      (Open.NormalPairRestriction.Constructions.openAmbientTransportMapsTo f Subtype.val (U).isOpenEmbedding') (2 * (p + q))
      (C).regularThomClass = integralProductOpenThomClass V W T πV πW hprod p q A B :=
  OpenNaturality.Constructions.complexThomClassInDegree_openAmbient U f
    (ProductOpenAnalytic.Constructions.integralProductOpenInclusion_contMDiff V W T πV πW hprod p q A B ω)
    (ProductOpenAnalytic.Constructions.integralProductOpenInclusion_mfderiv_injective V W T πV πW hprod p q A B)
    (ProductRegularOpen.Constructions.integralProductOpenInclusion_closed V W T πV πW hprod p q A B)
    ((C).contMDiff_regularComplementInclusion ω) (C).mfderiv_regularComplementInclusion_injective
    (C).isClosedEmbedding_regularComplementInclusion (p + q) (C).regularComplement_complexImmersionCodimension

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Integral.ProductOpen.Constructions
