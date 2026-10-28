import OAI.AlgebraicGeometry.Comparison.Betti.Affine.SchemeStalkNormalization
import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartGermFlatness

/-! # Scheme Stalk Flatness -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Affine.SchemeStalkFlatness

noncomputable section

/-! On an actual standard smooth affine open, the original
analytification structure-stalk map is flat. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Comparison.Betti.Affine.ChartGermFlatness.AnalyticLocal

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
  (U : X.left.Opens) (hU : IsAffineOpen U)
  [Algebra.IsStandardSmoothOfRelativeDimension (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
    ℂ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)]
  (e : OpenPartialHomeomorph (Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) (RegularSmoothness.NativeModel X))
  (he : e ∈ ComplexPoints.Analytic.SmoothSchemeManifold.affineRegularAtlas (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)
    (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom))
  (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U)) (hx : x ∈ e.source)

local notation "pointX" => OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU x

include e he hx in
theorem affineSectionHolomorphicStalkMap_flat (hp : Analytification.Base.analytificationMap X pointX ∈ U) :
    ((ConcreteHolomorphicStalkMap.algebraicHolomorphicStalkMap X pointX).comp (X.left.presheaf.germ U (Analytification.Base.analytificationMap X pointX) hp).hom).Flat := by
  let k := SchemeStalkNormalization.affineSchemeChartStalkEquiv X U hU e he x hx
  apply (RingHom.Flat.comp_iff_of_bijective_left (g := k.toRingHom) k.bijective).mp
  have hnorm : k.toRingHom.comp ((ConcreteHolomorphicStalkMap.algebraicHolomorphicStalkMap X pointX).comp
      (X.left.presheaf.germ U (Analytification.Base.analytificationMap X pointX) hp).hom) = ChartGermMap.AnalyticLocal.affineChartGermMap e he x hx := by
    apply RingHom.ext
    intro s
    exact SchemeStalkNormalization.affineSchemeChartStalkEquiv_algebraic_germ X U hU e he x hx hp s
  rw [hnorm]
  exact ChartGermFlatness.AnalyticLocal.standardSmooth_affineChartGermMap_flat e he x hx

include e he hx in
theorem affineAlgebraicHolomorphicStalkMap_flat (hp : Analytification.Base.analytificationMap X pointX ∈ U) :
    (ConcreteHolomorphicStalkMap.algebraicHolomorphicStalkMap X pointX).Flat := by
  let a : U := ⟨Analytification.Base.analytificationMap X pointX, hp⟩
  let : Algebra Γ(X.left, U) (X.left.presheaf.stalk (Analytification.Base.analytificationMap X pointX)) :=
    TopCat.Presheaf.algebra_section_stalk X.left.presheaf a
  let : IsLocalization.AtPrime (X.left.presheaf.stalk (Analytification.Base.analytificationMap X pointX))
      (hU.primeIdealOf a).asIdeal := hU.isLocalization_stalk a
  let : Algebra (X.left.presheaf.stalk (Analytification.Base.analytificationMap X pointX)) (ConcreteHolomorphicStalkMap.analyticHolomorphicStalk X pointX) :=
    (ConcreteHolomorphicStalkMap.algebraicHolomorphicStalkMap X pointX).toAlgebra
  let : Algebra Γ(X.left, U) (ConcreteHolomorphicStalkMap.analyticHolomorphicStalk X pointX) :=
    ((ConcreteHolomorphicStalkMap.algebraicHolomorphicStalkMap X pointX).comp (X.left.presheaf.germ U (Analytification.Base.analytificationMap X pointX) hp).hom).toAlgebra
  let : IsScalarTower Γ(X.left, U) (X.left.presheaf.stalk (Analytification.Base.analytificationMap X pointX))
      (ConcreteHolomorphicStalkMap.analyticHolomorphicStalk X pointX) := IsScalarTower.of_algebraMap_eq' rfl
  change Module.Flat (X.left.presheaf.stalk (Analytification.Base.analytificationMap X pointX)) (ConcreteHolomorphicStalkMap.analyticHolomorphicStalk X pointX)
  rw [Module.flat_iff_of_isLocalization (S := X.left.presheaf.stalk (Analytification.Base.analytificationMap X pointX))
    (p := (hU.primeIdealOf a).asIdeal.primeCompl)]
  exact affineSectionHolomorphicStalkMap_flat X U hU e he x hx hp

end

end OAI.AlgebraicGeometry.Comparison.Betti.Affine.SchemeStalkFlatness
