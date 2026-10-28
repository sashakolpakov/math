import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.EquationDivisor
import OAI.AlgebraicGeometry.CycleClass.Thom.Intersection.Gysin

/-! # Intersection Gysin -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.IntersectionGysin.Constructions

noncomputable section

/-! Intersecting the Thom class of an actual smooth closed algebraic
immersion with an equation gives the supported Thom pushforward of the
actual principal divisor on its source, with its scheme-order coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions
  Scheme.EquationDivisor.Constructions Scheme.SupportedPrincipalDivisor.Constructions Scheme.FiniteDivisorDetection.Constructions
  Intersection.Gysin.Constructions ImageIntersectionCup.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [AlgebraicGeometry.IsNoetherian X.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsClosedImmersion i.left]
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (Set.range (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion)ᶜ) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularThomClass)
  {L : Type} (v : L → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) (hv : IsOpen (Set.range v)ᶜ)
  {g : X.left.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left g) (hg : g ≠ 0)
  (hD : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' (Set.range v)ᶜ ⊆
    (Scheme.SectionEvaluation.Constructions.analyticOpen X D.domain : Set (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))))
  (f : (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⟶ PrincipalBoundary.Constructions.normalComplexLine) (hf : Set.MapsTo f (Set.range v)ᶜ PrincipalBoundary.Constructions.puncturedComplexLine)
  (hfg : ∀ x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' (Set.range v)ᶜ,
    f (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i x.val) 0 = Scheme.SectionEvaluation.Constructions.sectionEvaluationOn X D.domain
      (D.unit : Γ(X.left, D.domain)) ⟨x.val, hD x.property⟩)

include hg hfg

local instance : Fintype (Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain) := Fintype.ofFinite _

theorem imageIntersectionCup_eq_principalDivisor_gysin :
    ImageIntersectionCup.Constructions.imageIntersectionCup (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion v (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isClosed_range.isOpen_compl hv p 1
      (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularThomClass
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)) =
    (Intersection.Gysin.Constructions.intersectionGysinIso (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) a ha v hv).hom
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) hD 2
        (Scheme.SupportedPrincipalDivisor.Constructions.principalDivisorSupportedClass X D.domain g)) := by
  have he := Scheme.EquationDivisor.Constructions.pullback_equation_eq_principalDivisorSupportedClass X D hg
    (Y := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (Set.range v)ᶜ
    (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementTopCatMap hD f hf hfg
  have hc := Intersection.Gysin.Constructions.imageIntersectionCup_eq_gysin_pullback (q := 1)
    (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) a ha v hv
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1))
  exact hc.trans (congrArg
    (fun b => (Intersection.Gysin.Constructions.intersectionGysinIso (q := 1) (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) a ha v hv).hom b) he)

theorem imageIntersectionCup_eq_order_sum :
    ImageIntersectionCup.Constructions.imageIntersectionCup (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion v (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isClosed_range.isOpen_compl hv p 1
      (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularThomClass
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)) =
    ∑ z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain, (X.left.ord g z.val : ℚ) •
      (Intersection.Gysin.Constructions.intersectionGysinIso (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) a ha v hv).hom
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) hD 2
          (Scheme.SupportedPrincipalDivisor.Constructions.complementDivisorSupportedClass X D.domain z)) := by
  classical
  rw [imageIntersectionCup_eq_principalDivisor_gysin i p hp a ha v hv D hg hD f hf hfg]
  simp only [Scheme.SupportedPrincipalDivisor.Constructions.principalDivisorSupportedClass, map_sum, map_smul]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.IntersectionGysin.Constructions
