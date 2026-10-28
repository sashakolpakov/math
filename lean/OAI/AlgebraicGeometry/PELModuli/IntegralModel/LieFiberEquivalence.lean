import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.SectionLie
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieFiniteness
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.StalkLiftEquivalence
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.TangentBaseChange
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.PointsBaseChange

/-! # Lie Fiber Equivalence -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieFiberEquivalence

noncomputable section

/-! The actual Lie space of a geometric abelian fiber is the
relative infinitesimal space of the original family at its unit section. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

namespace AlgebraicLie
open OAI.AlgebraicGeometry.AbelianScheme.TorsionQuotient.SubgroupFunctor

variable {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {k : Type} [Field k] (q : Spec (.of k) ⟶ S)

theorem unitPoint_projection :
    (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.unitPoint (DualNumberReduction.AlgebraicLie.dualBase k) (A.pullback q).scheme).hom ≫ pullback.fst A.scheme.hom q =
      Affine.SectionLie.AffineSectionLie.zeroPoint η[A.scheme].left q := by
  let : GrpObj ((Over.pullback q).obj A.scheme) := (A.pullback q).group
  have h := congrArg Over.Hom.left
    (map_one (Group.PointsBaseChange.GroupPoints.baseChangePointsMulEquiv A.scheme q (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k)))
  change (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.unitPoint (DualNumberReduction.AlgebraicLie.dualBase k) (A.pullback q).scheme).hom ≫ pullback.fst A.scheme.hom q =
    (1 : Over.mk (DualNumberReduction.AlgebraicLie.dualBase k ≫ q) ⟶ A.scheme).left at h
  refine h.trans ?_
  change (DualNumberReduction.AlgebraicLie.dualBase k ≫ q) ≫ η[A.scheme].left = DualNumberReduction.AlgebraicLie.dualBase k ≫ q ≫ η[A.scheme].left
  exact Category.assoc _ _ _

def fiberRelativeEquiv : LiePoints.AlgebraicLie.Space (A.pullback q).scheme ≃ₗ[k]
    Affine.SectionLie.AffineSectionLie.Space A.scheme.hom η[A.scheme].left q := by
  let gp := (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.unitPoint (DualNumberReduction.AlgebraicLie.dualBase k) (A.pullback q).scheme).hom
  let gs := Affine.SectionLie.AffineSectionLie.zeroPoint η[A.scheme].left q
  let t := Relative.TangentBaseChange.RelativeTangent.map (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k)
    (A.pullback q).scheme.hom gp A.scheme.hom gs (pullback.fst A.scheme.hom q) q
    (pullback.condition) (unitPoint_projection A q)
  have ht : Function.Bijective t := Relative.TangentBaseChange.RelativeTangent.map_bijective_of_isPullback
    (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) (A.pullback q).scheme.hom gp A.scheme.hom gs
    (pullback.fst A.scheme.hom q) q (IsPullback.of_hasPullback A.scheme.hom q)
    (unitPoint_projection A q)
  let e : LiePoints.AlgebraicLie.Space (A.pullback q).scheme ≃ₗ[DualNumber k]
      Affine.SectionLie.AffineSectionLie.Space A.scheme.hom η[A.scheme].left q :=
    (StalkLiftEquivalence.groupTangentLocalEquiv (DualNumberReduction.AlgebraicLie.dualBase k) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) (A.pullback q).scheme).trans
      (LinearEquiv.ofBijective t ht)
  exact e.restrictScalars k

theorem fiberRelativeEquiv_point (v : LiePoints.AlgebraicLie.Space (A.pullback q).scheme) :
    Relative.TangentBaseChange.RelativeTangent.point (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) A.scheme.hom
        (Affine.SectionLie.AffineSectionLie.zeroPoint η[A.scheme].left q) (fiberRelativeEquiv A q v) =
      (LiePoints.AlgebraicLie.point (A.pullback q).scheme v).left ≫ pullback.fst A.scheme.hom q :=
  Relative.TangentBaseChange.RelativeTangent.point_map (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k)
    (A.pullback q).scheme.hom (AbelianScheme.TorsionQuotient.GroupTangentsEq.GroupTangents.unitPoint (DualNumberReduction.AlgebraicLie.dualBase k) (A.pullback q).scheme).hom
    A.scheme.hom (Affine.SectionLie.AffineSectionLie.zeroPoint η[A.scheme].left q) (pullback.fst A.scheme.hom q) q
    pullback.condition (unitPoint_projection A q)
    (StalkLiftEquivalence.groupTangentLocalEquiv (DualNumberReduction.AlgebraicLie.dualBase k) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) (A.pullback q).scheme v)

end AlgebraicLie

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieFiberEquivalence
