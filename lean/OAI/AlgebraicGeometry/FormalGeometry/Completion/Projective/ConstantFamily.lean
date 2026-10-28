import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Geometric.Projectivity

/-! # Constant Family -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily

noncomputable section

/-! Projective presentations of constant geometric group families and
the actual Cartesian squares obtained by changing their parameters. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

namespace Construction

universe u

def projectivePresentationOfSourceIso {S : Scheme.{u}} {X Y : Over S}
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation Y) (e : X ≅ Y) :
    AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X where
  dimension := P.dimension
  embedding := e.hom ≫ P.embedding
  closedImmersion := by
    have : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
    change IsClosedImmersion (e.hom.left ≫ P.embedding.left)
    infer_instance

variable {S : Scheme.{u}} (A T : Over S)

def tensorFamilyOver : Over T.left := Over.mk (fst T A).left

def tensorFamilyPullbackIso : tensorFamilyOver A T ≅ (Over.pullback T.hom).obj A :=
  Over.isoMk (pullbackSymmetry T.hom A.hom) (by simp [tensorFamilyOver])

def tensorFamilyProjectivePresentation (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A) :
    AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (tensorFamilyOver A T) :=
  projectivePresentationOfSourceIso (P.baseChange T.hom) (tensorFamilyPullbackIso A T)

theorem tensorFamily_isPullback {U : Over S} (j : U ⟶ T) :
    IsPullback (j ⊗ₘ 𝟙 A).left (fst U A).left (fst T A).left j.left := by
  have hf : (j ⊗ₘ 𝟙 A).left ≫ (fst T A).left = (fst U A).left ≫ j.left :=
    congrArg Over.Hom.left (tensorHom_fst j (𝟙 A))
  have hq : (j ⊗ₘ 𝟙 A).left ≫ (snd T A).left = (snd U A).left := by
    have h := congrArg Over.Hom.left (tensorHom_snd j (𝟙 A))
    change (j ⊗ₘ 𝟙 A).left ≫ (snd T A).left = (snd U A).left ≫ 𝟙 A.left at h
    rw [Category.comp_id] at h
    exact h
  apply IsPullback.of_right (t := (IsPullback.of_hasPullback T.hom A.hom).flip) ?_ hf
  change IsPullback ((j ⊗ₘ 𝟙 A).left ≫ (snd T A).left) (fst U A).left A.hom (j.left ≫ T.hom)
  rw [hq, j.w]
  exact (IsPullback.of_hasPullback U.hom A.hom).flip

def geometricGroupFamilyProjectivePresentation
    {K : Type u} [Field K] [IsAlgClosed K]
    (A T : Over (Spec (CommRingCat.of K))) [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyIntegral A.hom] :
    AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation (tensorFamilyOver A T) :=
  tensorFamilyProjectivePresentation A T (Classical.choice (Geometric.Projectivity.Construction.geometric_group_projectivePresentation A))

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Projective.ConstantFamily
