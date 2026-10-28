import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.Pullbacks
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.PullbackRecoveryIso

/-! # Identity Affine Family Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The identity affine presentation of a relative projective closed family is canonically isomorphic to the actual original family, compatibly with its embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : CommRingCat.{u}} {n : ℕ} (F : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver (Spec R) n))

def Closed.Families.FlatClosedFamily.identityAffineFamilyMap : (F.affineProjectivePullback (𝟙 _)).scheme.left ⟶ F.scheme.left :=
  (F.ideal.comapIso (AffineProjective.Charts.affineProjectiveChartMap (𝟙 _) n)).hom ≫
    Limits.pullback.snd (AffineProjective.Charts.affineProjectiveChartMap (𝟙 _) n) F.ideal.subschemeι

theorem Closed.Families.FlatClosedFamily.identityAffineFamilyMap_isPullback :
    IsPullback F.identityAffineFamilyMap (F.affineProjectivePullback (𝟙 _)).scheme.hom F.scheme.hom (𝟙 _) :=
  ClosedFamily.Transport.closedFamilyTransport_isPullback (AffineProjective.Charts.affineProjectiveChartMap (𝟙 _) n) (𝟙 _)
    (AffineProjective.Charts.affineProjectiveChartMap_isPullback (𝟙 _) n) F.ideal

instance Closed.Families.FlatClosedFamily.identityAffineFamilyMap_isIso : IsIso F.identityAffineFamilyMap :=
  F.identityAffineFamilyMap_isPullback.isIso_fst_of_isIso

def Closed.Families.FlatClosedFamily.identityAffineFamilyIso : (F.affineProjectivePullback (𝟙 _)).scheme ≅ F.scheme :=
  Over.isoMk (asIso F.identityAffineFamilyMap)
    (F.identityAffineFamilyMap_isPullback.w.trans (Category.comp_id _))

theorem Closed.Families.FlatClosedFamily.identityAffineFamilyIso_embedding :
    F.identityAffineFamilyIso.hom.left ≫ F.inclusion.left =
      (F.affineProjectivePullback (𝟙 _)).inclusion.left ≫ AffineProjective.Charts.affineProjectiveChartMap (𝟙 _) n :=
  ClosedFamily.PullbackRecoveryIso.closedFamilyTransport_embedding F.ideal (AffineProjective.Charts.affineProjectiveChartMap (𝟙 _) n)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
