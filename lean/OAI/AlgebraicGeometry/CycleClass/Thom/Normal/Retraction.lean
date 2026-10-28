import OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.Retraction
import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.TwoSupportCup
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportRelative

/-! # Retraction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Retraction.Constructions

noncomputable section

/-! Pushing a source normal-equation class through the actual local
Thom isomorphism concatenates its normal coordinates with the ambient
normal coordinates, with coefficient one and the original support. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Immersion.Retraction.Constructions OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalSupportRelative.Constructions
  IntersectionCup.Constructions Intersection.TwoSupportCup.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    V.analyticSpace (Z.regularThomComplementOpen : Set V.analyticSpace)) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass)
  (x : Z.regularAnalyticSpace)
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ) Z.regularComplementInclusion x)

abbrev normalRetractionThomIso
    (O : Opens (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding)) (n : ℕ) :=
  Immersion.Retraction.Constructions.retractionThomIso Z a ha P.openNeighborhood (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P Z.closed.isEmbedding)
    (HodgeConjecture.DegreeTwo.NormalPairSourceRetraction.Constructions.normalPairSourceInclusion_retraction P Z.closed.isEmbedding) O n

theorem normalRetractionThomIso_normal
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)))
    (O : Opens (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding)) {q : ℕ}
    (g : TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding) ⟶ TopCat.of (Fin q → ℂ))
    (hg : Set.MapsTo g (O : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding)) {0}ᶜ)
    (e : ((Fin p → ℂ) × (Fin q → ℂ)) ≃L[ℂ] (Fin (p + q) → ℂ)) :
    eqToHom (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of P.neighborhood)
      (P.relativeComplement ∪ (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P Z.closed.isEmbedding) ⁻¹'
        (O : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding))) n) (Nat.mul_add 2 p q).symm)
      ((normalRetractionThomIso Z a ha x P O (2 * q)).hom
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg (2 * q)
          (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass q))) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (IntersectionCup.Constructions.internalNormalMap P.normalCoordinate (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P Z.closed.isEmbedding ≫ g) e)
      (IntersectionCup.Constructions.internalNormalMapsTo P.normalCoordinate (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P Z.closed.isEmbedding ≫ g)
        P.normalCoordinate_mapsTo (fun _ hx => hg hx) e)
      (2 * (p + q)) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (p + q)) := by
  let r := HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P Z.closed.isEmbedding
  let B : Opens P.neighborhood :=
    ⟨r ⁻¹' (O : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding)),
      O.isOpen.preimage r.hom.continuous⟩
  let b := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g hg (2 * q)
    (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass q)
  have hc := ConcreteCategory.congr_hom
    (Immersion.Retraction.Constructions.retractionThomIso_eq_cup Z a ha P.openNeighborhood r
      (HodgeConjecture.DegreeTwo.NormalPairSourceRetraction.Constructions.normalPairSourceInclusion_retraction P Z.closed.isEmbedding) O (2 * q)) b
  change (normalRetractionThomIso Z a ha x P O (2 * q)).hom b =
    HodgeConjecture.DegreeTwo.SupportCup.Constructions.twoSupportCohomologyCup (TopCat.of P.neighborhood) P.relativeComplement (B : Set P.neighborhood)
      (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P) B.isOpen (2 * p) (2 * q)
      (Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ) V.analyticSpace
        (Set.range Z.regularComplementInclusion)ᶜ P.openNeighborhood (2 * p) Z.regularThomClass)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) r
        (A := (B : Set P.neighborhood)) (B := (O : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding)))
        (fun _ hx => hx) (2 * q) b) at hc
  have hz := Z.regularThomClass_restrict_normalPair x P hP
  have hg' := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) r g
      (A := (B : Set P.neighborhood)) (B := (O : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding)))
      (C := {0}ᶜ) (fun _ hx => hx) hg (2 * q)) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass q)
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) r
      (A := (B : Set P.neighborhood)) (B := (O : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding)))
      (fun _ hx => hx) (2 * q) b =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (r ≫ g) (fun _ hx => hg hx)
      (2 * q) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass q) at hg'
  rw [hz, hg'] at hc
  have hd := congrArg (fun t => eqToHom (congrArg
    (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood)
      (P.relativeComplement ∪ (B : Set P.neighborhood)) n) (Nat.mul_add 2 p q).symm) t) hc
  exact hd.trans ((Intersection.TwoSupportCup.Constructions.evenIntersectionCup_eq_twoSupport (TopCat.of P.neighborhood)
    P.relativeComplement (B : Set P.neighborhood) (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P) B.isOpen p q
      (P.normalCohomologyMap (ModuleCat.of ℚ ℚ) (2 * p) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (r ≫ g) (fun _ hx => hg hx)
        (2 * q) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass q))).symm.trans
    (IntersectionCup.Constructions.evenIntersectionCup_normalized_pullbacks P.normalCoordinate (r ≫ g) P.normalCoordinate_mapsTo
      (fun _ hx => hg hx) e (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPair_relativeComplement_isOpen P) B.isOpen))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Retraction.Constructions
