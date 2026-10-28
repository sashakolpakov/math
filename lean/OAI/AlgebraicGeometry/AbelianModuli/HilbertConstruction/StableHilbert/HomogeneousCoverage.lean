import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.ClosedFamilyTwisting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyKernelRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationSectionData

/-! # Homogeneous Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.HomogeneousCoverage.StableHilbertCoverage

noncomputable section

/-! The canonical saturated homogeneous model of an original relative
projective embedding retains its precise embedding and twisting bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

private theorem inverse_embedding_square {C : Type*} [Category* C]
    {W X Y Z T : C} (a : W ⟶ X) (e : Y ≅ X) (i : X ⟶ T)
    (j : Y ⟶ Z) (q : Z ⟶ T) (h : e.hom ≫ i = j ≫ q) :
    ((a ≫ e.inv) ≫ j) ≫ q = a ≫ i := by
  rw [Category.assoc, Category.assoc, ← h, e.inv_hom_id_assoc]

namespace RelativeModel
variable {R : CommRingCat.{u}} {n : ℕ}
variable (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver (Spec R) n))

def ideal : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) :=
  (F.affineProjectivePullback (𝟙 _)).homogeneousIdeal

def iso : Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (ideal F) ≅ F.scheme :=
  (F.affineProjectivePullback (𝟙 _)).homogeneousFamilyIso ≪≫ F.identityAffineFamilyIso

theorem embedding :
    (iso F).hom.left ≫ F.inclusion.left =
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (ideal F) ≫ AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec R)) n := by
  let G := F.affineProjectivePullback (𝟙 _)
  change (G.homogeneousFamilyIso.hom.left ≫ F.identityAffineFamilyIso.hom.left) ≫
    F.inclusion.left = _
  rw [Category.assoc, F.identityAffineFamilyIso_embedding, ← Category.assoc]
  exact congrArg (fun a => a ≫ AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec R)) n)
    (congrArg Over.Hom.left G.homogeneousFamilyIso_embedding)

end RelativeModel

namespace EmbeddingModel
variable {R : CommRingCat.{u}} {n : ℕ} {X : Over (Spec R)}
variable (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec R) n)
variable [IsClosedImmersion i.left] [Flat X.hom] [LocallyOfFinitePresentation X.hom]

def ideal : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) :=
  RelativeModel.ideal (Closed.Families.FlatClosedFamily.ofEmbedding i)

theorem saturated : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.IsSaturated (ideal i).toIdeal :=
  ((Closed.Families.FlatClosedFamily.ofEmbedding i).affineProjectivePullback (𝟙 _)).homogeneousIdeal_saturated

def iso : X ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily (ideal i) :=
  Closed.Families.FlatClosedFamily.ofEmbeddingIso i ≪≫ (RelativeModel.iso (Closed.Families.FlatClosedFamily.ofEmbedding i)).symm

theorem embedding :
    ((iso i).hom.left ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (ideal i)) ≫
      AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec R)) n = i.left := by
  let F := Closed.Families.FlatClosedFamily.ofEmbedding i
  exact (inverse_embedding_square (Closed.Families.FlatClosedFamily.ofEmbeddingIso i).hom.left
    ((Over.forget _).mapIso (RelativeModel.iso F)) F.inclusion.left
    (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (ideal i)) (AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec R)) n)
    (RelativeModel.embedding F)).trans
      (congrArg Over.Hom.left (Closed.Families.FlatClosedFamily.ofEmbeddingIso_inclusion i))

def twistingIso :
    ((ProjectiveTwisting.Bundle.projectiveTwistingBundle (ideal i) 1).pullback (iso i).hom.left).sheaf ≅
      ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec R) n).pullback i.left).sheaf := by
  let e := (iso i).hom.left
  let j := HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (ideal i)
  let a := AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec R)) n
  let L := RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec R) n
  let M := Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n
  exact (Scheme.Modules.pullback e).mapIso (ProjectiveTwisting.TwistingRestriction.affineProjectiveTwistingBundle_quotientIso (ideal i)).symm ≪≫
    (Scheme.Modules.pullbackComp e j).app M.sheaf ≪≫
    (Scheme.Modules.pullback (e ≫ j)).mapIso (Relative.TwistingAffinePullback.relativeProjectiveTwistingBundle_affineIso (𝟙 (Spec R)) n).symm ≪≫
    (Scheme.Modules.pullbackComp (e ≫ j) a).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (embedding i)).app L.sheaf

end EmbeddingModel

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.HomogeneousCoverage.StableHilbertCoverage
