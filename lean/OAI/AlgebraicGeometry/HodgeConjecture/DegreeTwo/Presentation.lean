import OAI.AlgebraicGeometry.Betti.ProjectivePresentationCohomology
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveHodgeNaturality

/-! # Presentation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Presentation.Constructions

noncomputable section

/-! An actual Hodge class on an integral projective variety satisfies the componentwise Hodge predicate of its original smooth projective presentation. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false

theorem presentation_isRationalHodgeClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (α : V.rationalCohomology (p+p)) (hα : V.IsRationalHodgeClass p α) :
    V.presentation.IsRationalHodgeClass p α := by
  apply (V.presentation.isRationalHodgeClass_iff_components p α).mpr
  intro C
  rw [V.presentation.componentBettiEquiv_apply]
  exact Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.isRationalHodgeClass_pullback
    (V.presentation.componentInclusionOver C) p hα

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Presentation.Constructions
