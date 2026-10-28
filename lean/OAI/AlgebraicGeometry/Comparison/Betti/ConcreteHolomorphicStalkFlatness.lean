import OAI.AlgebraicGeometry.Comparison.Betti.Affine.SchemeStalkFlatness
import OAI.AlgebraicGeometry.Comparison.Betti.RegularSmoothness
import OAI.AlgebraicGeometry.Comparison.Betti.ConcreteHolomorphicStalkLocal
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-! # Concrete Holomorphic Stalk Flatness -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ConcreteHolomorphicStalkFlatness

noncomputable section

/-! The original algebraic-to-holomorphic structure-sheaf morphism
is faithfully flat on every actual stalk of a smooth integral complex
scheme. All maps are normalized on their original regular sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem algebraicHolomorphicStalkMap_flat (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    (ConcreteHolomorphicStalkMap.algebraicHolomorphicStalkMap X p).Flat := by
  obtain ⟨U, hU, hstd, x, e, he, hx, hxp⟩ := RegularSmoothness.exists_standardSmooth_scheme_affine_chart X p
  let : Algebra.IsStandardSmoothOfRelativeDimension (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)
      ℂ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U) := hstd
  have hpU : Analytification.Base.analytificationMap X (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU x) ∈ U := by
    have hmem : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU x ∈
        Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU) := ⟨x, rfl⟩
    rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap] at hmem
    exact hmem
  exact (congrArg (fun q : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X => (ConcreteHolomorphicStalkMap.algebraicHolomorphicStalkMap X q).Flat) hxp).mp
    (Affine.SchemeStalkFlatness.affineAlgebraicHolomorphicStalkMap_flat X U hU e he x hx hpU)

theorem algebraicHolomorphicStalkMap_faithfullyFlat (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    (ConcreteHolomorphicStalkMap.algebraicHolomorphicStalkMap X p).FaithfullyFlat := by
  let : Algebra (X.left.presheaf.stalk (Analytification.Base.analytificationMap X p)) (ConcreteHolomorphicStalkMap.analyticHolomorphicStalk X p) :=
    (ConcreteHolomorphicStalkMap.algebraicHolomorphicStalkMap X p).toAlgebra
  let : Module.Flat (X.left.presheaf.stalk (Analytification.Base.analytificationMap X p)) (ConcreteHolomorphicStalkMap.analyticHolomorphicStalk X p) :=
    algebraicHolomorphicStalkMap_flat X p
  let : IsLocalHom (algebraMap (X.left.presheaf.stalk (Analytification.Base.analytificationMap X p)) (ConcreteHolomorphicStalkMap.analyticHolomorphicStalk X p)) :=
    ConcreteHolomorphicStalkLocal.algebraicHolomorphicStalkMap_isLocalHom X p
  change Module.FaithfullyFlat (X.left.presheaf.stalk (Analytification.Base.analytificationMap X p)) (ConcreteHolomorphicStalkMap.analyticHolomorphicStalk X p)
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end

end OAI.AlgebraicGeometry.Comparison.Betti.ConcreteHolomorphicStalkFlatness
