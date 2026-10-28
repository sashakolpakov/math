import OAI.AlgebraicGeometry.CycleClass.Geometric.InjectiveHomotopyRestriction
import OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSubdivision
import OAI.AlgebraicGeometry.CycleClass.Geometric.SubdivisionHomotopy
import OAI.AlgebraicTopology.Cohomology.Singular.NaturalSmallChains

/-! # Small Subdivision Homotopy -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSubdivisionHomotopy.Cycles

noncomputable section

/-!
# The actual subdivision homotopy on small singular chains

The ambient subdivision homotopy is natural under every continuous map.
Consequently each component preserves cover-small chains: every such simplex
factors through a single member of the cover. We restrict these actual
components through the injective small-chain inclusion, and prove their
homotopy identity using that inclusion.

No openness or covering assumption is needed for this restriction. Those
hypotheses enter only the separate eventual-smallness theorem.
-/

open _root_.CategoryTheory

variable (X : TopCat.{0}) {J : Type} (U : J → Set X)

/-- Every component of the actual ambient subdivision homotopy preserves
the actual image of the small-chain inclusion. -/
theorem subdivisionHomotopy_preserves_smallChainImage (a b : ℕ)
    {c : (LocalHomology.Cycles.integralSingularChains X).X a}
    (hc : c ∈ LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f a).hom) :
    (SubdivisionHomotopy.Cycles.subdivisionHomotopy X).hom a b c ∈
      LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f b).hom :=
  AlgebraicTopology.Cohomology.Singular.NaturalSmallChains.naturalSingularOperation_preserves_smallChainImage
    (SubdivisionHomotopy.Cycles.naturalSubdivisionHomotopy.hom a b) X U hc

/-- The genuine barycentric subdivision chain map on small chains is
homotopic to the identity, by restriction of the constructed ambient homotopy. -/
def smallSubdivisionHomotopy :
    Homotopy (SmallSubdivision.Cycles.smallSubdivisionChainMap X U) (𝟙 (SmallChainImage.Cycles.integralSmallSingularChains X U)) :=
  InjectiveHomotopyRestriction.Cycles.restrictHomotopy (SmallChainImage.Cycles.smallIntegralChainInclusion X U)
    (SmallChainImage.Cycles.smallIntegralChainInclusion_injective X U)
    (SmallSubdivision.Cycles.smallSubdivisionChainMap_intertwining X U) (by simp)
    (SubdivisionHomotopy.Cycles.subdivisionHomotopy X)
    (fun a b c => subdivisionHomotopy_preserves_smallChainImage X U a b
      (LinearMap.mem_range_self _ c))

/-- Inclusion identifies each restricted homotopy component with the actual
ambient component. -/
@[reassoc]
theorem smallSubdivisionHomotopy_inclusion (a b : ℕ) :
    (smallSubdivisionHomotopy X U).hom a b ≫
        (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f b =
      (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f a ≫ (SubdivisionHomotopy.Cycles.subdivisionHomotopy X).hom a b :=
  InjectiveHomotopyRestriction.Cycles.restrictedHomotopyComponent_comp _ _ _ _ a b

/-- The same compatibility evaluated on an actual small chain. -/
@[simp]
theorem smallSubdivisionHomotopy_apply_inclusion (a b : ℕ)
    (c : (SmallChainImage.Cycles.integralSmallSingularChains X U).X a) :
    (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f b ((smallSubdivisionHomotopy X U).hom a b c) =
      (SubdivisionHomotopy.Cycles.subdivisionHomotopy X).hom a b ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f a c) :=
  InjectiveHomotopyRestriction.Cycles.restrictedHomotopyComponent_apply _ _ _ _ a b c

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SmallSubdivisionHomotopy.Cycles
