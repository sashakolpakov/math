import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.FamilyIdealVanishing
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FamilyEquationParameterIdeal

/-! # Family Equation Locus -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations

noncomputable section

/-! A natural morphism equation with projective source has an actual
closed solution locus on every locally noetherian parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
variable {M : Over S} [IsLocallyNoetherian M.left]

theorem Endomorphisms.Core.FamilyMorphismEquation.projective_closed_locus
    (r : Endomorphisms.Core.FamilyMorphismEquation F) (B : Has.Core.ProjectivePresentation r.source)
    (φ : yoneda.obj M ⟶ F) :
    ∃ (Z : Over S) (j : Z ⟶ M), IsClosedImmersion j.left ∧
      ∀ (T : Over S) (x : T ⟶ M),
        r.lhs.app (.op T) (φ.app (.op T) x) =
          r.rhs.app (.op T) (φ.app (.op T) x) ↔
            ∃! y : T ⟶ Z, y ≫ j = x := by
  let : Flat r.source.hom := r.flat
  let : IsProper r.source.hom := r.proper
  let : LocallyOfFinitePresentation r.source.hom := r.finitelyPresented
  obtain ⟨Z, j, hj, htest, _⟩ := Projective.FamilyIdealVanishing.Core.projective_family_ideal_vanishing_closed_locus B
    (r.parameterIdeal φ)
  refine ⟨Z, j, hj, ?_⟩
  intro T x
  exact (r.parameterIdeal_comap_eq_bot_iff φ x).symm.trans (htest T x)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations
