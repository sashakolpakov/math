import OAI.AlgebraicGeometry.CycleClass.Thom.Open.RestrictionNormalPair
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.NormalPairRestriction

/-! # Thom Open Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction.Constructions

noncomputable section

/-! The original supported Thom class restricts to the actual Thom
class of the open restriction, including when its source is truncated. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ImmersionOpenRestriction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.RestrictionNormalPair.Constructions
  Open.NormalNeighborhoodInverse.Constructions.PairTransport Degree.Constructions.ThomClass

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem pairMap_congr {X Y : TopCat.{0}} {A : Set X} {B : Set Y}
    {f g : X ⟶ Y} (h : f = g) (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf n =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg n := by
  subst g
  rfl

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p) (U : Opens V.analyticSpace)

local instance : MetrizableSpace U := U.isOpenEmbedding'.isEmbedding.metrizableSpace

theorem regularThomClass_open_normal (x : Closed.ImmersionOpenRestriction.Constructions.sourceOpen Z U)
    (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ)
      (Closed.ImmersionOpenRestriction.Constructions.restrict Z U).regularComplementInclusion x)
    (hQ : Q.ambientChart.MDifferentiable 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ))) :
    Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (Set.range (Closed.ImmersionOpenRestriction.Constructions.restrict Z U).regularComplementInclusion)ᶜ Q.openNeighborhood (2 * p)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (Geometric.LocalHomology.Cycles.subspaceInclusion V.analyticSpace (U : Set V.analyticSpace))
        (Open.RestrictionNormalPair.Constructions.restriction_mapsTo Z U) (2 * p) Z.regularThomClass) = Q.rationalClassFin := by
  let P := Open.RestrictionNormalPair.Constructions.liftedNormalPair Z U x Q
  let k := Open.NormalNeighborhoodInverse.Constructions.PairTransport.openTransportNormalNeighborhoodMap Q Subtype.val U.isOpenEmbedding'
  have h₁ := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of U) Q.neighborhood)
      (Geometric.LocalHomology.Cycles.subspaceInclusion V.analyticSpace (U : Set V.analyticSpace))
      (A := Q.relativeComplement) (B := (Set.range (Closed.ImmersionOpenRestriction.Constructions.restrict Z U).regularComplementInclusion)ᶜ)
      (C := (Set.range Z.regularComplementInclusion)ᶜ) (fun _ hx => hx)
      (Open.RestrictionNormalPair.Constructions.restriction_mapsTo Z U) (2 * p)) Z.regularThomClass
  have h₂ := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) k
      (Geometric.LocalHomology.Cycles.subspaceInclusion V.analyticSpace P.neighborhood)
      (A := Q.relativeComplement) (B := P.relativeComplement)
      (C := (Set.range Z.regularComplementInclusion)ᶜ)
      (Open.RestrictionNormalPair.Constructions.liftedNeighborhood_mapsTo Z U x Q) (fun _ hx => hx) (2 * p)) Z.regularThomClass
  have he := h₁.trans h₂.symm
  change Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (Set.range (Closed.ImmersionOpenRestriction.Constructions.restrict Z U).regularComplementInclusion)ᶜ Q.openNeighborhood (2 * p)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (Geometric.LocalHomology.Cycles.subspaceInclusion V.analyticSpace (U : Set V.analyticSpace))
        (Open.RestrictionNormalPair.Constructions.restriction_mapsTo Z U) (2 * p) Z.regularThomClass) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) k (Open.RestrictionNormalPair.Constructions.liftedNeighborhood_mapsTo Z U x Q) (2 * p)
      (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) V.analyticSpace
        (Set.range Z.regularComplementInclusion)ᶜ P.openNeighborhood (2 * p) Z.regularThomClass) at he
  rw [Z.regularThomClass_restrict_normalPair x.val P (Open.RestrictionNormalPair.Constructions.liftedNormalPair_mdifferentiable Z U x Q hQ)] at he
  have hn := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) k P.normalCoordinate
      (Open.RestrictionNormalPair.Constructions.liftedNeighborhood_mapsTo Z U x Q) P.normalCoordinate_mapsTo (2 * p))
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)
  have hk : k ≫ P.normalCoordinate = Q.normalCoordinate := Open.RestrictionNormalPair.Constructions.liftedNeighborhood_normalCoordinate Z U x Q
  rw [Q.rationalClassFin_eq_normalPullback]
  apply he.trans
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) k (Open.RestrictionNormalPair.Constructions.liftedNeighborhood_mapsTo Z U x Q) (2 * p)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) P.normalCoordinate P.normalCoordinate_mapsTo
        (2 * p) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) Q.normalCoordinate Q.normalCoordinate_mapsTo
      (2 * p) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)
  apply hn.trans
  exact ConcreteCategory.congr_hom
    (pairMap_congr hk (P.normalCoordinate_mapsTo.comp (Open.RestrictionNormalPair.Constructions.liftedNeighborhood_mapsTo Z U x Q))
      Q.normalCoordinate_mapsTo (2 * p)) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p)

theorem regularThomClass_open_restriction :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (Geometric.LocalHomology.Cycles.subspaceInclusion V.analyticSpace (U : Set V.analyticSpace))
      (Open.RestrictionNormalPair.Constructions.restriction_mapsTo Z U) (2 * p) Z.regularThomClass = (Closed.ImmersionOpenRestriction.Constructions.restrict Z U).regularThomClass := by
  let D := Closed.ImmersionOpenRestriction.Constructions.restrict Z U
  apply Degree.Constructions.ThomClass.complexThomClassInDegree_unique (E := Z.regularAnalyticModel) (F := V.analyticModel)
    (M := Closed.ImmersionOpenRestriction.Constructions.sourceOpen Z U) (N := U) D.regularComplementInclusion D.holomorphic
    D.differential_injective D.closed p D.regularComplement_complexImmersionCodimension
    D.regularFixedNormalPair D.regularFixedNormalPair_ambientChart_mdifferentiable
  intro x
  exact regularThomClass_open_normal Z U x (D.regularFixedNormalPair x)
    (D.regularFixedNormalPair_ambientChart_mdifferentiable x)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction.Constructions
