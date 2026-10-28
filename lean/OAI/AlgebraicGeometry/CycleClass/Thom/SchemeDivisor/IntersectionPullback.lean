import OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.IntersectionGlobalGysin
import OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo

/-! # Intersection Pullback -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.IntersectionPullback.Constructions

noncomputable section

/-! The genuine equation-intersection order sum commutes with an actual
ambient pair map, retaining the intersection support of every term. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.ClosedImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.Gysin.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.SupportEnlargement.Constructions
  Scheme.FiniteDivisorDetection.Constructions Scheme.SectionEvaluation.Constructions Supported.GysinEnlargement.Constructions
  IntersectionGlobalGysin.Constructions ImageIntersectionCup.Constructions ImageIntersectionTo.Constructions.Restriction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
  [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [AlgebraicGeometry.IsNoetherian X.left]
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)]
  (i : X ⟶ Y) [IsClosedImmersion i.left]
  (p : ℕ) (hp : Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom + p =
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom)
  {L : Type} (v : L → ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)
  {N M P : Type} [TopologicalSpace N] (u : M → N) (w : P → N)
  (F : TopCat.of N ⟶ TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y))
  (hF : Set.MapsTo F (Set.range u)ᶜ (Set.range (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion)ᶜ)
  (hG : Set.MapsTo F (Set.range w)ᶜ (Set.range v)ᶜ)

include hF hG in
omit [AlgebraicGeometry.IsNoetherian X.left] [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)] in
theorem pullbackDivisor_mapsTo (R : X.left.Opens) (z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X R)
    (hR : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' (Set.range v)ᶜ ⊆ (Scheme.SectionEvaluation.Constructions.analyticOpen X R : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) :
    Set.MapsTo F (Set.range u ∩ Set.range w)ᶜ (Gysin.Constructions.divisorImageOpen i ⟨z.val, z.property.1⟩ : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) :=
  fun _ hx => Supported.GysinEnlargement.Constructions.target_mapsTo (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (Gysin.Constructions.divisorImageOpen i ⟨z.val, z.property.1⟩)
    (Gysin.Constructions.divisorImage_supported i ⟨z.val, z.property.1⟩ p hp) v (SupportEnlargement.Constructions.complement_le_divisorImageOpen i R z v hR)
    (ImageIntersectionTo.Constructions.Restriction.intersectionMapsTo (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion v u w F hF hG hx)

variable (a : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ)
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) (Set.range (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion)ᶜ) (2 * p))
  (ha : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (2 * p) a = (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularThomClass)
  (hv : IsOpen (Set.range v)ᶜ) (hu : IsOpen (Set.range u)ᶜ) (hw : IsOpen (Set.range w)ᶜ)
  {g : X.left.functionField} (D : RationalFunctionBoundary.Constructions.Principal.RationalUnitRepresentative X.left g)

local instance : Fintype (Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain) := Fintype.ofFinite _

include hv in
theorem imageIntersectionCup_pullback_eq_order_globalGysin_sum
    (hg : g ≠ 0)
    (hD : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' (Set.range v)ᶜ ⊆ (Scheme.SectionEvaluation.Constructions.analyticOpen X D.domain : Set (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
    (f : (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)) ⟶ PrincipalBoundary.Constructions.normalComplexLine)
    (hf : Set.MapsTo f (Set.range v)ᶜ PrincipalBoundary.Constructions.puncturedComplexLine)
    (hfg : ∀ x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i ⁻¹' (Set.range v)ᶜ,
      f (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i x.val) 0 = Scheme.SectionEvaluation.Constructions.sectionEvaluationOn X D.domain
        (D.unit : Γ(X.left, D.domain)) ⟨x.val, hD x.property⟩) :
    ImageIntersectionCup.Constructions.imageIntersectionCup u w hu hw p 1
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) F hF (2 * p)
        (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularThomClass)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) F hG 2
        (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f hf 2 (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1))) =
    ∑ z : Scheme.FiniteDivisorDetection.Constructions.ComplementDivisorPoint X D.domain, (X.left.ord g z.val : ℚ) •
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) F
        (pullbackDivisor_mapsTo i p hp v u w F hF hG D.domain z hD) (2 * (p + 1))
        (Gysin.Constructions.divisorGysinClass i ⟨z.val, z.property.1⟩ p hp a ha) := by
  classical
  rw [← ImageIntersectionTo.Constructions.Restriction.imageIntersectionCup_restriction (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion v u w F hF hG
    (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).closed.isClosed_range.isOpen_compl hv hu hw p 1]
  rw [IntersectionGlobalGysin.Constructions.imageIntersectionCup_eq_order_globalGysin_sum i p hp a ha v hv D hg hD f hf hfg]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl ?_
  intro z _
  apply congrArg (fun b => (X.left.ord g z.val : ℚ) • b)
  exact ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) F (𝟙 (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y)))
      (ImageIntersectionTo.Constructions.Restriction.intersectionMapsTo (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp).regularComplementInclusion v u w F hF hG)
      (Supported.GysinEnlargement.Constructions.target_mapsTo (Scheme.ClosedImmersion.Constructions.schemeClosedImmersion i p hp) (Gysin.Constructions.divisorImageOpen i ⟨z.val, z.property.1⟩)
        (Gysin.Constructions.divisorImage_supported i ⟨z.val, z.property.1⟩ p hp) v (SupportEnlargement.Constructions.complement_le_divisorImageOpen i D.domain z v hD))
      (2 * (p + 1))) (Gysin.Constructions.divisorGysinClass i ⟨z.val, z.property.1⟩ p hp a ha)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.SchemeDivisor.IntersectionPullback.Constructions
