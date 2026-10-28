import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.PullbackRecoveryIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.FamilyKernelRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.TwistingAffinePullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.Pullbacks
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.TwistingBundle

/-! # Pullback Embedding Twisting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PullbackEmbeddingTwisting

noncomputable section

/-! The affine field presentation of a relative closed embedding recovers
the actual pulled-back source and the pulled-back embedding line bundle. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme.{u}} {X : Over S} {n : ℕ}
variable (j : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
variable [Flat X.hom] [LocallyOfFinitePresentation X.hom]
variable {R : CommRingCat.{u}} (x : Spec R ⟶ S)

def affinePullbackEmbeddingIso :
    (Over.pullback x).obj X ≅ ((Closed.Families.FlatClosedFamily.ofEmbedding j).affineProjectivePullback x).scheme :=
  (Over.pullback x).mapIso (Closed.Families.FlatClosedFamily.ofEmbeddingIso j) ≪≫
    ((Closed.Families.FlatClosedFamily.ofEmbedding j).pullbackAlongIso (AffineProjective.Charts.affineProjectiveChartMap x n) x
      (AffineProjective.Charts.affineProjectiveChartMap_isPullback x n)).symm

theorem affinePullbackEmbeddingIso_inclusion :
    (affinePullbackEmbeddingIso j x).hom ≫
        ((Closed.Families.FlatClosedFamily.ofEmbedding j).affineProjectivePullback x).inclusion ≫
          (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso (AffineProjective.Charts.affineProjectiveChartMap x n) x
            (AffineProjective.Charts.affineProjectiveChartMap_isPullback x n)).hom =
      (Over.pullback x).map j := by
  let F := Closed.Families.FlatClosedFamily.ofEmbedding j
  let e := F.pullbackAlongIso (AffineProjective.Charts.affineProjectiveChartMap x n) x
    (AffineProjective.Charts.affineProjectiveChartMap_isPullback x n)
  change ((Over.pullback x).map (Closed.Families.FlatClosedFamily.ofEmbeddingIso j).hom ≫ e.inv) ≫
    (F.affineProjectivePullback x).inclusion ≫
      (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso (AffineProjective.Charts.affineProjectiveChartMap x n) x
        (AffineProjective.Charts.affineProjectiveChartMap_isPullback x n)).hom = _
  erw [Category.assoc, ← F.pullbackAlongIso_inclusion (AffineProjective.Charts.affineProjectiveChartMap x n) x
      (AffineProjective.Charts.affineProjectiveChartMap_isPullback x n)]
  change (Over.pullback x).map (Closed.Families.FlatClosedFamily.ofEmbeddingIso j).hom ≫
    e.inv ≫ e.hom ≫ (Over.pullback x).map F.inclusion = _
  rw [Iso.inv_hom_id_assoc, ← Functor.map_comp, Closed.Families.FlatClosedFamily.ofEmbeddingIso_inclusion]

theorem affinePullbackEmbeddingIso_embedding :
    (affinePullbackEmbeddingIso j x).hom.left ≫
        ((Closed.Families.FlatClosedFamily.ofEmbedding j).affineProjectivePullback x).inclusion.left ≫
          AffineProjective.Charts.affineProjectiveChartMap x n =
      pullback.fst X.hom x ≫ j.left := by
  let hp := AffineProjective.Charts.affineProjectiveChartMap_isPullback x n
  have h := congrArg (fun k : (Over.pullback x).obj X ⟶
      (Over.pullback x).obj (Projective.ProjectivePresentations.projectiveSpaceOver S n) =>
      k.left ≫ pullback.fst (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom x)
    (affinePullbackEmbeddingIso_inclusion j x)
  change (((affinePullbackEmbeddingIso j x).hom.left ≫
      ((Closed.Families.FlatClosedFamily.ofEmbedding j).affineProjectivePullback x).inclusion.left) ≫
      hp.isoPullback.hom) ≫ pullback.fst (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom x = _ at h
  rw [Category.assoc, hp.isoPullback_hom_fst, Category.assoc] at h
  exact h.trans (pullback.lift_fst _ _ _)

def affinePullbackEmbeddingTwistingIso :
    ((((Closed.Families.FlatClosedFamily.ofEmbedding j).affineProjectivePullback x).twistingBundle).pullback
      (affinePullbackEmbeddingIso j x).hom.left).sheaf ≅
    (((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n).pullback j.left).pullback (pullback.fst X.hom x)).sheaf := by
  let O := RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S n
  let F := (Closed.Families.FlatClosedFamily.ofEmbedding j).affineProjectivePullback x
  let e := (affinePullbackEmbeddingIso j x).hom.left
  let c := AffineProjective.Charts.affineProjectiveChartMap x n
  exact (Scheme.Modules.pullback e).mapIso
      ((Scheme.Modules.pullback F.inclusion.left).mapIso (Relative.TwistingAffinePullback.relativeProjectiveTwistingBundle_affineIso x n).symm) ≪≫
    (Scheme.Modules.pullback e).mapIso
      ((Scheme.Modules.pullbackComp F.inclusion.left c).app O.sheaf) ≪≫
    (Scheme.Modules.pullbackComp e (F.inclusion.left ≫ c)).app O.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (affinePullbackEmbeddingIso_embedding j x)).app O.sheaf ≪≫
    (Scheme.Modules.pullbackComp (pullback.fst X.hom x) j.left).symm.app O.sheaf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PullbackEmbeddingTwisting
