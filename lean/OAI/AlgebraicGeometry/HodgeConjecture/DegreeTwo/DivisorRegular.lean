import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.RegularSectionFixedPair
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FinOneNormalResidue
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorWinding

/-! # Divisor Regular -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorRegular.Constructions.DivisorRegularThom

noncomputable section

/-!
# DegreeTwo: divisor multiplicity in the actual global regular Thom class

The actual rational-section supported class agrees locally with its
algebraic order times restriction of the global regular-support Thom
class, with the proved universal nonzero winding normalization.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorWinding.Constructions.DivisorEvaluation

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (L : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle V.presentation)
  (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V 1) (U : V.carrier.Opens)
  (x : Z.regularAnalyticSpace)
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin 1 → ℂ)
    Z.regularComplementInclusion x)
  (hPU : ∀ y ∈ P.neighborhood, y.val ∈ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U)

/-- Inclusion of the actual normal neighborhood into the original
algebraic open, via the actual regular ambient-open inclusion. -/
def neighborhoodInclusion : TopCat.of P.neighborhood ⟶ TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U) :=
  TopCat.ofHom ⟨fun y => ⟨y.val.val, hPU y.val y.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

def referenceComplement : Set P.neighborhood :=
  (neighborhoodInclusion Z U x P hPU) ⁻¹' L.referenceLocus U

theorem referenceComplement_mapsTo :
    Set.MapsTo (neighborhoodInclusion Z U x P hPU) (referenceComplement L Z U x P hPU)
      (L.referenceLocus U) := fun _ hy => hy

/-- Exact local comparison with the existing global regular Thom class.
The integer is the actual section exponent supplied by the divisor DVR
calculation; negative orders are included. -/
theorem rationalSectionLocalClass_eq_regularThom [Nonempty U]
    (i : V.carrier) (hi : U ≤ L.trivializingOpen i)
    (p : Γ(V.carrier, U)) (hp : p ≠ 0) (v : Γ(V.carrier, U)ˣ)
    (m : ℤ) (hm : m ≠ 0)
    (he : (L.rationalSectionCoordinate i : V.carrier.functionField) =
      V.carrier.germToFunctionField U v * (V.carrier.germToFunctionField U p) ^ m)
    (hmd : P.ambientChart.MDifferentiable 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, Z.regularAnalyticModel × (Fin 1 → ℂ)))
    (hcoord : ∀ y : P.neighborhood, P.normalCoordinate y 0 =
      DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p (neighborhoodInclusion Z U x P hPU y)) :
    ∃ hA : referenceComplement L Z U x P hPU ⊆ P.relativeComplement,
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (neighborhoodInclusion Z U x P hPU)
        (referenceComplement_mapsTo L Z U x P hPU) 2 (L.rationalSectionLocalSupportedClass i U hi) =
      m • ((-WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient) •
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of P.neighborhood)) hA 2
          (CycleClass.Geometric.RelativeCohomologySections.Cycles.relativeCohomologyOpenRestriction (ModuleCat.of ℚ ℚ)
            (TopCat.of Z.regularAmbientSpace) (Set.range Z.regularComplementInclusion)ᶜ
            P.openNeighborhood 2 Z.regularThomClass)) := by
  let A := referenceComplement L Z U x P hPU
  let j := neighborhoodInclusion Z U x P hPU
  have hA : A ⊆ P.relativeComplement := by
    intro y hy hsupport
    have hn := DivisorWinding.Constructions.DivisorEvaluation.referenceParameter_ne_zero L i U hi p hp v m hm he ⟨j y, hy⟩
    apply hn
    change DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn V.presentation U p (j y) = 0
    rw [← hcoord y]
    have hz := (P.mem_range_iff y).mp hsupport
    exact congrFun hz 0
  refine ⟨hA, ?_⟩
  rw [Z.regularThomClass_restrict_normalPair x P hmd,
    ← P.rationalClassFin_eq_normalPullback,
    DivisorWinding.Constructions.DivisorEvaluation.rationalSectionLocalSupportedClass_power L i U hi p hp v m hm he, map_zsmul]
  congr 1
  let s : C(A, ℂ) := (DivisorWinding.Constructions.DivisorEvaluation.referenceParameter L U p).comp
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceMap j (referenceComplement_mapsTo L Z U x P hPU)).hom
  have hs : ∀ y, s y ≠ 0 := fun y =>
    DivisorWinding.Constructions.DivisorEvaluation.referenceParameter_ne_zero L i U hi p hp v m hm he
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceMap j (referenceComplement_mapsTo L Z U x P hPU) y)
  have hn := DivisorClass.Chern.Supported.Winding.supportedWindingClass_pullback (TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen V.presentation U))
    (L.referenceLocus U) j A (referenceComplement_mapsTo L Z U x P hPU)
    (DivisorWinding.Constructions.DivisorEvaluation.referenceParameter L U p) (DivisorWinding.Constructions.DivisorEvaluation.referenceParameter_ne_zero L i U hi p hp v m hm he)
  exact hn.trans (FinOneNormalResidue.Constructions.finOne_equation_supportedWindingClass P A hA s hs
    (fun y => (hcoord y.val).symm))

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorRegular.Constructions.DivisorRegularThom
