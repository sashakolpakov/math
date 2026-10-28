import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.SchemeDifferentiable
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicAlgebraizationGraph

/-! # Map -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Map

noncomputable section

/-! The actual holomorphic generating map is an actual algebraic morphism, by the verified proper graph algebraization theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem exists_holomorphicSection_algebraic_map (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) {n : ℕ}
    (s : Fin (n + 1) → Data.HolomorphicLineSection u ⊤)
    (hs : ∀ x : V.analyticSpace, ∃ j, Nonzero.holomorphicSectionNonzeroAt u (s j) x) :
    ∃ g : V.toOver ⟶ (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver,
      ∀ x, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = SchemeDifferentiable.holomorphicSectionSchemeMap V u s hs x := by
  let : IsIntegral V.toOver.left := V.property
  let : Smooth V.toOver.hom := V.presentation.smooth
  let : IsProper V.toOver.hom := V.presentation.isProper
  let : Nonempty (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints V.toOver) := V.analyticSpace_nonempty
  let : CompactSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints V.toOver) := V.analyticSpace_compactSpace
  let : IsIntegral (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver.left := (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).property
  let : Smooth (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver.hom := (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).presentation.smooth
  let : IsProper (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver.hom := (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).presentation.isProper
  exact Geometry.ComplexTorus.RiemannProjectivity.HolomorphicAlgebraizationGraph.Constructions.HolomorphicAlgebraization.exists_algebraic_map V.presentation.projective
    (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).presentation.projective (SchemeDifferentiable.holomorphicSectionSchemeMap V u s hs)
      (SchemeDifferentiable.holomorphicSectionSchemeMap_mdifferentiable V u s hs)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Map
