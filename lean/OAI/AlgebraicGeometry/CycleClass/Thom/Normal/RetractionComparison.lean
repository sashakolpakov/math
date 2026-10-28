import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Retraction
import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.RetractionEquations
import OAI.AlgebraicGeometry.CycleClass.Thom.Normal.RetractionZeroLocus
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition
import OAI.AlgebraicGeometry.CycleClass.Thom.Equation

/-! # Retraction Comparison -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normal.RetractionComparison.Constructions

noncomputable section

/-! In a genuine normal neighborhood, supported Thom pushforward of
a source submersion equation is the actual Thom class of its ambient
zero locus. Both the support and the complex orientation are retained. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.ClosedImmersionComposition.Constructions.ComplexManifold OAI.AlgebraicGeometry.CycleClass.Thom.Normal.Retraction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normal.RetractionEquations.Constructions
  RetractionZeroLocus.Constructions IntersectionCup.Constructions Equation.Constructions.ThomClass
  ExteriorImageCup.Constructions.Restriction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)
  (x : Z.regularAnalyticSpace)
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ) Z.regularComplementInclusion x)

local instance : ChartedSpace V.analyticModel P.neighborhood :=
  inferInstanceAs (ChartedSpace V.analyticModel P.openNeighborhood)

def sourceEquationOpen {q : ℕ}
    (g : TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding) ⟶ TopCat.of (Fin q → ℂ)) :
    Opens (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding) :=
  ⟨g ⁻¹' {0}ᶜ, isClosed_singleton.isOpen_compl.preimage g.hom.continuous⟩

variable {q : ℕ}
  (C : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion (Open.ClosedImmersionComposition.Constructions.ComplexManifold.openManifold V P.openNeighborhood) (p + q))
  (g : TopCat.of (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding) ⟶ TopCat.of (Fin q → ℂ))
  (hC : Set.range C.regularComplementInclusion =
    (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P Z.closed.isEmbedding) '' (g ⁻¹' {0}))

include hC in
theorem thomSupport_eq :
    P.relativeComplement ∪ (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P Z.closed.isEmbedding) ⁻¹'
      (sourceEquationOpen Z x P g : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding)) =
    (Set.range C.regularComplementInclusion)ᶜ :=
  (RetractionZeroLocus.Constructions.equations_support_complement P Z.closed.isEmbedding g).trans (congrArg Set.compl hC.symm)

variable
  (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, V.analyticModel)
    𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)))
  (hq : ContMDiffOn 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)) ω
    P.ambientChart P.ambientChart.source)
  (hqi : ContMDiffOn 𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)) 𝓘(ℂ, V.analyticModel) ω
    P.ambientChart.symm P.ambientChart.target)
  (hg : ContMDiff 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, Fin q → ℂ) ω g)
  (hgs : ∀ y : HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding, g y = 0 →
    Function.Surjective (mfderiv 𝓘(ℂ, Z.regularAnalyticModel) 𝓘(ℂ, Fin q → ℂ) g y))

include hC hP hq hqi hg hgs

theorem normalRetractionThomIso_eq_Thom
    (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
      V.analyticSpace (Z.regularThomComplementOpen : Set V.analyticSpace)) (2 * p))
    (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = Z.regularThomClass) :
    eqToHom (congrArg (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of P.neighborhood) A (2 * (p + q))) (thomSupport_eq Z x P C g hC))
      (eqToHom (congrArg (fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of P.neighborhood)
        (P.relativeComplement ∪ (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P Z.closed.isEmbedding) ⁻¹'
          (sourceEquationOpen Z x P g : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding))) n)
        (Nat.mul_add 2 p q).symm)
        ((Retraction.Constructions.normalRetractionThomIso Z a ha x P (sourceEquationOpen Z x P g) (2 * q)).hom
          (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) g
            (A := (sourceEquationOpen Z x P g : Set (HodgeConjecture.DegreeTwo.NormalPairProductSupport.Constructions.normalPairSourceOpen P Z.closed.isEmbedding)))
            (B := {0}ᶜ) (fun _ hx => hx) (2 * q) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass q)))) =
      C.regularThomClass := by
  let e := HodgeConjecture.DegreeTwo.LocalProductCoefficient.Constructions.productFlattenCoordinates p q
  let H := IntersectionCup.Constructions.internalNormalMap P.normalCoordinate (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P Z.closed.isEmbedding ≫ g) e
  have hzero : ∀ y, y ∈ Set.range C.regularComplementInclusion ↔ H y = 0 := by
    intro y
    rw [hC]
    exact (RetractionZeroLocus.Constructions.equations_zero_iff P Z.closed.isEmbedding g e y).symm
  have hs : ∀ z : C.regularAnalyticSpace, Function.Surjective
      (mfderiv 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Fin (p + q) → ℂ) H (C.regularComplementInclusion z)) := by
    intro z
    have hz : C.regularComplementInclusion z ∈
        (HodgeConjecture.DegreeTwo.NormalPairSourceSupport.Constructions.normalPairSourceInclusionMap P Z.closed.isEmbedding) '' (g ⁻¹' {0}) :=
      hC ▸ Set.mem_range_self z
    obtain ⟨y, hy, hiy⟩ := hz
    rw [← hiy]
    exact RetractionEquations.Constructions.equations_submersion Z x P hP hq hqi g hg e y (hgs y hy)
  have hthom := Equation.Constructions.ThomClass.equation_pullback_eq_Thom C H hzero
    (RetractionEquations.Constructions.equations_analytic Z x P hq hqi g hg e) hs
  have hn := Retraction.Constructions.normalRetractionThomIso_normal Z a ha x P hP (sourceEquationOpen Z x P g) g
    (fun _ hx => hx) e
  have ht := congrArg (fun b => eqToHom (congrArg
    (fun A => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of P.neighborhood) A
      (2 * (p + q))) (thomSupport_eq Z x P C g hC)) b) hn
  exact ht.trans ((ExteriorImageCup.Constructions.Restriction.relativeCohomologyMap_sourceCast H (thomSupport_eq Z x P C g hC)
    (IntersectionCup.Constructions.internalNormalMapsTo P.normalCoordinate (HodgeConjecture.DegreeTwo.SourceThomProjection.Constructions.normalPairSourceRetractionMap P Z.closed.isEmbedding ≫ g)
      P.normalCoordinate_mapsTo (fun _ hx => hx) e)
    (Equation.Constructions.ThomClass.equation_mapsTo C H hzero) (2 * (p + q)) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass (p + q))).trans hthom)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normal.RetractionComparison.Constructions
