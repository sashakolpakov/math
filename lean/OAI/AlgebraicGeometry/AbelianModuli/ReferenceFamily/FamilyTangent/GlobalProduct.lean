import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.CorrectedCoverData
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.MappedCoverCoverage

/-! # Global Product -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.GlobalProduct

noncomputable section

/-! A primitive of the actual linear tangent cocycle constructs a
global isomorphism from the actual tangent family to the constant
original fixed fiber. Both open covers and both glued inverse maps are
constructed from the original affine cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Algebra ℂ R] [Algebra R ℂ] [IsScalarTower ℂ R ℂ]
    (X : Over (Spec (.of R))) [Smooth X.hom] [IsSeparated X.hom]
    (U : X.left.AffineOpenCover) (d : Derivation ℂ R ℂ)
    (a : Primitives.fixedFamilyDerivationGauges R X U) (ha : Primitives.IsFamilyTangentDerivationPrimitive R X U d a)

attribute [local implicit_reducible] Affine.OpenDiagram.familyAffineOpenDiagram Fixed.ProductFunctor.fixedFamilyProductFunctor

local instance tangentGlobalProduct_mapOpen {B C : Scheme} (f : B ⟶ C)
    {Y Z : Over C} (i : Y ⟶ Z) [IsOpenImmersion i.left] :
    IsOpenImmersion ((Over.pullback f).map i).left := OverPullbackCartesianMap.overPullback_map_open f i

def familyTangentGlobalProduct : TangentBasePoint.tangentFamily ℂ R X d ≅
    (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).obj (TangentBasePoint.fixedFamilyFiber ℂ R X) := by
  let A : U.I₀ → Over (Spec (.of R)) := fun i =>
    (Affine.OpenDiagram.familyAffineOpenDiagram X).obj (Family.AffineCoverIntersections.familyCoverAffineOpen R X U i)
  let j : ∀ i, A i ⟶ X := fun i => HilbertConstruction.Open.ParameterPoints.openParameterInclusion X (Family.AffineCoverIntersections.familyCoverAffineOpen R X U i).1
  have hc : ∀ x : X.left, ∃ i, x ∈ (j i).left.opensRange := Family.MappedCoverCoverage.familyAffineCover_inclusions_covers R X U
  let p := Spec.map (CommRingCat.ofHom (algebraMap R ℂ))
  have hF := Family.MappedCoverCoverage.overPullback_indexed_covers (TangentBasePoint.tangentBasePoint ℂ R d) A j hc
  have hG₀ := Family.MappedCoverCoverage.overPullback_indexed_covers p A j hc
  have hG := Family.MappedCoverCoverage.overPullback_indexed_covers (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)
    (fun i => (Over.pullback p).obj (A i)) (fun i => (Over.pullback p).map (j i)) hG₀
  exact (Family.CorrectedCoverData.familyCorrectedCoverData R X U d a ha).glue hF hG

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FamilyTangent.GlobalProduct
