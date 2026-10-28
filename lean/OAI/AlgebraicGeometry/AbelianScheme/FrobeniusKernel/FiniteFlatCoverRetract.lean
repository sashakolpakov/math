import OAI.AlgebraicGeometry.PELModuli.CMPoints.FiniteFlatRetract
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.IntrinsicRetracts

/-! # Finite Flat Cover Retract -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteFlatCoverRetract.Construction

noncomputable section

/-! Retraction over the target preserves a finite flat surjective cover.
The cover is an actual scheme over that target; no relative group structure is required. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {G B : Over S}

theorem over_retract_surjective [Surjective G.hom]
    (r : G ⟶ B) : Surjective B.hom := by
  constructor
  intro s
  obtain ⟨g, hg⟩ := (inferInstance : Surjective G.hom).surj s
  refine ⟨r.left g, ?_⟩
  exact (congrArg (fun f : G.left ⟶ S => f g) r.w).trans hg

theorem finite_flat_cover_of_over_retract
    [IsFinite G.hom] [Flat G.hom] [LocallyOfFinitePresentation G.hom] [Surjective G.hom]
    (i : B ⟶ G) (r : G ⟶ B) (h : i ≫ r = 𝟙 B) :
    IsFinite B.hom ∧ Flat B.hom ∧ LocallyOfFinitePresentation B.hom ∧ Surjective B.hom := by
  have : IsFinite B.hom := CartierDuality.IntrinsicRetracts.Construction.Schemes.finite_of_over_retract i r h
  obtain ⟨hf, hp⟩ := PELModuli.CMPoints.FiniteFlatRetract.finite_flat_scheme_retract_general G B i r h
  exact ⟨inferInstance, hf, hp, over_retract_surjective r⟩

theorem finite_flat_cover_of_open_closed_restriction
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) (f : Y ⟶ Z)
    [IsOpenImmersion i] [IsClosedImmersion i] [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] [Nonempty X] [Subsingleton Z] :
    IsFinite (i ≫ f) ∧ Flat (i ≫ f) ∧ LocallyOfFinitePresentation (i ≫ f) ∧
      Surjective (i ≫ f) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  constructor
  intro z
  exact ⟨Classical.choice (inferInstance : Nonempty X), Subsingleton.elim _ _⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FiniteFlatCoverRetract.Construction
