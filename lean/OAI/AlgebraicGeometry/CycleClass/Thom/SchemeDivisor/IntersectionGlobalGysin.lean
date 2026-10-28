import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.IntersectionGysin
import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.SupportEnlargement

/-! # Intersection Global Gysin -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.IntersectionGlobalGysin.Constructions

noncomputable section

/-! The supported equation intersection is the sum of the genuine global divisor
Gysin classes for an arbitrary smooth algebraic ambient scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Module.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Gysin.Constructions
  SupportEnlargement.Constructions Scheme.SupportedPrincipalDivisor.Constructions Scheme.FiniteDivisorDetection.Constructions
  Scheme.SectionEvaluation.Constructions Supported.GysinEnlargement.Constructions Normal.GysinRestriction.Constructions Intersection.Gysin.Constructions
  Normal.Product.Constructions.Class IntersectionGysin.Constructions ImageIntersectionCup.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [AlgebraicGeometry.IsNoetherian X.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsClosedImmersion i.left]
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
  (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (Set.range (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion)ᶜ) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularThomClass)
  {L : Type} (v : L → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) (hv : IsOpen (Set.range v)ᶜ)

theorem gysin_enlargedDivisorClass_to_global
    (R : X.left.Opens) (z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X R)
    (hR : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' (Set.range v)ᶜ ⊆ (Scheme.SectionEvaluation.Constructions.analyticOpen X R : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) :
    (Intersection.Gysin.Constructions.intersectionGysinIso (q := 1) (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) a ha v hv).hom
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) hR 2
        (Scheme.SupportedPrincipalDivisor.Constructions.complementDivisorSupportedClass X R z)) =
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
      (Supported.GysinEnlargement.Constructions.target_mapsTo (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (Gysin.Constructions.divisorImageOpen i ⟨z.val, z.property.1⟩)
        (Gysin.Constructions.divisorImage_supported i ⟨z.val, z.property.1⟩ p hp) v (SupportEnlargement.Constructions.complement_le_divisorImageOpen i R z v hR))
      (2 * (p + 1)) (Gysin.Constructions.divisorGysinClass i ⟨z.val, z.property.1⟩ p hp a ha) := by
  let W := Gysin.Constructions.divisorImageOpen i ⟨z.val, z.property.1⟩
  have hW := Gysin.Constructions.divisorImage_supported i ⟨z.val, z.property.1⟩ p hp
  have hOW := SupportEnlargement.Constructions.complement_le_divisorImageOpen i R z v hR
  have hs := SupportEnlargement.Constructions.enlargedDivisorClass_eq_gysinSource i R z v hR p hp
  have hg := ConcreteCategory.congr_hom
    (Supported.GysinEnlargement.Constructions.globalGysinIso_enlargement (q := 1) (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) W hW v hv hOW a ha)
    ((AlgebraicTopology.Duality.Poincare.SupportCohomologyMayerVietoris.relativeRationalCohomologyCongr (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (Gysin.Constructions.divisorSourceComplement i ⟨z.val, z.property.1⟩) 2).inv (Module.Constructions.supportedDivisorClass X ⟨z.val, z.property.1⟩))
  exact (congrArg (fun b => (Intersection.Gysin.Constructions.intersectionGysinIso (q := 1) (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) a ha v hv).hom b) hs).trans hg

variable {g : X.left.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left g)

local instance : Fintype (Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain) := Fintype.ofFinite _

theorem imageIntersectionCup_eq_order_globalGysin_sum
    (hg : g ≠ 0)
    (hD : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' (Set.range v)ᶜ ⊆ (Scheme.SectionEvaluation.Constructions.analyticOpen X D.domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
    (f : (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⟶ PrincipalBoundary.Constructions.normalComplexLine)
    (hf : Set.MapsTo f (Set.range v)ᶜ PrincipalBoundary.Constructions.puncturedComplexLine)
    (hfg : ∀ x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' (Set.range v)ᶜ,
      f (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i x.val) 0 = Scheme.SectionEvaluation.Constructions.sectionEvaluationOn X D.domain
        (D.unit : Γ(X.left, D.domain)) ⟨x.val, hD x.property⟩) :
    ImageIntersectionCup.Constructions.imageIntersectionCup (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion v
      (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isClosed_range.isOpen_compl hv p 1
      (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularThomClass
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)) =
    ∑ z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain, (X.left.ord g z.val : ℚ) •
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
        (Supported.GysinEnlargement.Constructions.target_mapsTo (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (Gysin.Constructions.divisorImageOpen i ⟨z.val, z.property.1⟩)
          (Gysin.Constructions.divisorImage_supported i ⟨z.val, z.property.1⟩ p hp) v (SupportEnlargement.Constructions.complement_le_divisorImageOpen i D.domain z v hD))
        (2 * (p + 1)) (Gysin.Constructions.divisorGysinClass i ⟨z.val, z.property.1⟩ p hp a ha) := by
  classical
  refine (IntersectionGysin.Constructions.imageIntersectionCup_eq_order_sum i p hp a ha v hv D hg hD f hf hfg).trans ?_
  refine Finset.sum_congr rfl ?_
  intro z _
  exact congrArg (fun b => (X.left.ord g z.val : ℚ) • b)
    (gysin_enlargedDivisorClass_to_global i p hp a ha v hv D.domain z hD)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.IntersectionGlobalGysin.Constructions
