import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SectionCoverProjective

/-! # Cartesian Family -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CartesianFamily

noncomputable section

/-! Projective presentations of Cartesian constant product families from
affine section covers of the two factors. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.CartesianFamilyProjective

theorem separated {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [IsProper f] : X.IsSeparated :=
  ⟨by rw [← terminal.comp_from f]; infer_instance⟩

variable {A B X Y S T : Scheme.{u}} [IsAffine S] [IsAffine T]
variable (a : A ⟶ T) (b : B ⟶ T) (f : X ⟶ S) (g : Y ⟶ S)
variable (p : X ⟶ A) (q : Y ⟶ B) (t : S ⟶ T)
variable (hp : IsPullback p f a t) (hq : IsPullback q g b t)

def sectionCover (DA : AffineSectionOf.Construction.AffineSectionCover.Data A) (DB : AffineSectionOf.Construction.AffineSectionCover.Data B) :
    AffineSectionOf.Construction.AffineSectionCover.Data (pullback f g) := by
  have : MorphismProperty.IsStableUnderBaseChange (@IsAffineHom : MorphismProperty Scheme.{u}) :=
    isAffineHom_isStableUnderBaseChange
  have : IsAffineHom t := inferInstance
  have : IsAffineHom p := MorphismProperty.of_isPullback hp.flip ‹IsAffineHom t›
  have : IsAffineHom q := MorphismProperty.of_isPullback hq.flip ‹IsAffineHom t›
  exact (DA.pullback p).product (DB.pullback q) f g

def presentation [IsProper f] [IsProper g]
    (DA : AffineSectionOf.Construction.AffineSectionCover.Data A) (DB : AffineSectionOf.Construction.AffineSectionCover.Data B) :
    AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (Over.mk (pullback.fst f g ≫ f)) :=
  (sectionCover a b f g p q t hp hq DA DB).projectivePresentation (pullback.fst f g ≫ f)

end Construction.CartesianFamilyProjective

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CartesianFamily
