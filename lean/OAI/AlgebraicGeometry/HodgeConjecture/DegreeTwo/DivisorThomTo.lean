import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorWinding
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.EquationThomResidue

/-! # Divisor Thom To -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorThomTo.Constructions.DivisorThomResidue

noncomputable section

/-!
# DegreeTwo: actual rational-section divisor order in a local Thom class

The regular equation and its actual algebraic integer order determine the
supported rational-section class in a genuine normal neighborhood. Enlarging
support to the reference divisor uses the actual relative map of pairs.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorWinding.Constructions.DivisorEvaluation

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle X) [IsIntegral X.carrier]
  (U : X.carrier.Opens) (p : Γ(X.carrier, U))
  (x : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U) (hxp : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p x = 0)
  {d : ℕ}
  (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair (Fin d → ℂ) ℂ
    (Subtype.val : {y : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U // DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y = 0} → DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U)
    ⟨x, hxp⟩)

def neighborhoodInclusion : TopCat.of P.neighborhood ⟶ TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def referenceComplement : Set P.neighborhood := {y | y.val ∈ L.referenceLocus U}

theorem referenceComplement_mapsTo :
    Set.MapsTo (neighborhoodInclusion U p x hxp P) (referenceComplement L U p x hxp P)
      (L.referenceLocus U) := fun _ hy => hy

/-- The actual algebraic divisor exponent multiplies the actual normal
Thom class after mapping to the reference support. -/
theorem rationalSectionLocalClass_eq_localThom [Nonempty U]
    (i : X.carrier) (hi : U ≤ L.trivializingOpen i)
    (hp : p ≠ 0) (v : Γ(X.carrier, U)ˣ) (m : ℤ) (hm : m ≠ 0)
    (he : (L.rationalSectionCoordinate i : X.carrier.functionField) =
      X.carrier.germToFunctionField U v * (X.carrier.germToFunctionField U p) ^ m)
    (hP : ∀ y : P.neighborhood, P.normalCoordinate y = DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y.val) :
    ∃ hA : referenceComplement L U p x hxp P ⊆ P.relativeComplement,
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (neighborhoodInclusion U p x hxp P)
        (referenceComplement_mapsTo L U p x hxp P) 2 (L.rationalSectionLocalSupportedClass i U hi) =
      m • ((-WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient) •
        AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
          (𝟙 (TopCat.of P.neighborhood)) hA 2 (NormalMultiplicity.Constructions.normalChartClass P)) := by
  let A := referenceComplement L U p x hxp P
  have hA : A ⊆ P.relativeComplement := by
    intro y hy hsupport
    obtain ⟨z, hz⟩ := hsupport
    have hn := DivisorWinding.Constructions.DivisorEvaluation.referenceParameter_ne_zero L i U hi p hp v m hm he ⟨y.val, hy⟩
    apply hn
    change DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p y.val = 0
    rw [← hz]
    exact z.property
  refine ⟨hA, ?_⟩
  rw [DivisorWinding.Constructions.DivisorEvaluation.rationalSectionLocalSupportedClass_power L i U hi p hp v m hm he, map_zsmul]
  congr 1
  have hn := DivisorClass.Chern.Supported.Winding.supportedWindingClass_pullback (TopCat.of (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U)) (L.referenceLocus U)
    (neighborhoodInclusion U p x hxp P) A (referenceComplement_mapsTo L U p x hxp P)
    (DivisorWinding.Constructions.DivisorEvaluation.referenceParameter L U p) (DivisorWinding.Constructions.DivisorEvaluation.referenceParameter_ne_zero L i U hi p hp v m hm he)
  have ht := EquationThomResidue.Constructions.equation_supportedWindingClass_support_extension (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U p)
    x hxp P hP A hA
  exact hn.trans ht

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.DivisorThomTo.Constructions.DivisorThomResidue
