import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.Product
import OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup

/-! # Product Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProductRestriction.Constructions

noncomputable section

/-! The exterior cup of actual supported algebraic cycle classes restricts
to the genuine Thom class of their product regular-locus immersion. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

open OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ExteriorImageCup.Constructions.Restriction OAI.AlgebraicGeometry.CycleClass.Thom.Regular.Product.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V W : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p q : ℕ}
  (A : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : Geometric.DimensionCycles.DimensionCycleSupport W q)

def supportedExteriorCycleClass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
    (TopCat.of (V.analyticSpace × W.analyticSpace))
    (Set.range (Prod.map A.analyticInclusion B.analyticInclusion))ᶜ (2 * (p + q)) :=
  ExteriorImageCup.Constructions.imageExteriorCup A.analyticInclusion B.analyticInclusion
    A.isClosedEmbedding_analyticInclusion.isClosed_range.isOpen_compl
    B.isClosedEmbedding_analyticInclusion.isClosed_range.isOpen_compl p q
    A.rationalSupportedCycleClass B.rationalSupportedCycleClass

def regularProductAmbientMap : TopCat.of (A.regularAmbientSpace × B.regularAmbientSpace) ⟶
    TopCat.of (V.analyticSpace × W.analyticSpace) :=
  AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) A.analyticSingularBoundaryᶜ,
    Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of W.analyticSpace) B.analyticSingularBoundaryᶜ) :
    (TopCat.of A.regularAmbientSpace, TopCat.of B.regularAmbientSpace) ⟶
      (TopCat.of V.analyticSpace, TopCat.of W.analyticSpace))

theorem regularProductAmbientMap_mapsTo : Set.MapsTo (regularProductAmbientMap A B)
    (Set.range (Prod.map A.regularComplementInclusion B.regularComplementInclusion))ᶜ
    (Set.range (Prod.map A.analyticInclusion B.analyticInclusion))ᶜ :=
  ExteriorImageCup.Constructions.Restriction.productImageRestrictionMapsTo A.regularComplementInclusion B.regularComplementInclusion
    A.analyticInclusion B.analyticInclusion
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) A.analyticSingularBoundaryᶜ)
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of W.analyticSpace) B.analyticSingularBoundaryᶜ)
    (fun x hx => (A.mem_regularThomComplement_iff x).mp hx)
    (fun x hx => (B.mem_regularThomComplement_iff x).mp hx)

theorem supportedExteriorCycleClass_regularRestriction :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (regularProductAmbientMap A B)
      (regularProductAmbientMap_mapsTo A B) (2 * (p + q)) (supportedExteriorCycleClass A B) =
      Regular.Product.Constructions.regularProductThomClass A B := by
  have h := ExteriorImageCup.Constructions.Restriction.imageExteriorCup_restriction A.regularComplementInclusion B.regularComplementInclusion
    A.analyticInclusion B.analyticInclusion
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of V.analyticSpace) A.analyticSingularBoundaryᶜ)
    (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of W.analyticSpace) B.analyticSingularBoundaryᶜ)
    (fun x hx => (A.mem_regularThomComplement_iff x).mp hx)
    (fun x hx => (B.mem_regularThomComplement_iff x).mp hx)
    A.isClosedEmbedding_regularComplementInclusion.isClosed_range.isOpen_compl
    B.isClosedEmbedding_regularComplementInclusion.isClosed_range.isOpen_compl
    A.isClosedEmbedding_analyticInclusion.isClosed_range.isOpen_compl
    B.isClosedEmbedding_analyticInclusion.isClosed_range.isOpen_compl p q
    A.rationalSupportedCycleClass B.rationalSupportedCycleClass
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (regularProductAmbientMap A B)
    (regularProductAmbientMap_mapsTo A B) (2 * (p + q)) (supportedExteriorCycleClass A B) =
    ExteriorImageCup.Constructions.imageExteriorCup A.regularComplementInclusion B.regularComplementInclusion _ _ p q
      (A.regularThomCohomologyRestriction (ModuleCat.of ℚ ℚ) (2 * p) A.rationalSupportedCycleClass)
      (B.regularThomCohomologyRestriction (ModuleCat.of ℚ ℚ) (2 * q) B.rationalSupportedCycleClass) at h
  rw [A.rationalSupportedCycleClass_regularPullback, B.rationalSupportedCycleClass_regularPullback,
    ← Regular.Product.Constructions.regularProductThomClass_eq_exterior] at h
  exact h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Supported.ProductRestriction.Constructions
