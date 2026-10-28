import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieFiberEquivalence
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.AffineLieNaturality
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieAlgebraic

/-! # Lie Family Differential -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieFamilyDifferential

noncomputable section

/-! The geometric-fiber Lie comparison intertwines the actual
pulled-back integral action with the relative differential on the family. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

namespace AlgebraicLie

variable {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  {k R : Type} [Field k] [CommRing R] (q : Spec (.of k) ⟶ S) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction R A)

def familyDifferential (a : R) : Module.End k (Affine.SectionLie.AffineSectionLie.Space A.scheme.hom η[A.scheme].left q) :=
  Section.AffineLieNaturality.AffineSectionLie.map A.scheme.hom A.scheme.hom η[A.scheme].left η[A.scheme].left q
    (ρ.map a).left (ρ.map a).w (congrArg Over.Hom.left (IsMonHom.one_hom (ρ.map a)))

theorem familyDifferential_point (a : R) (v : Affine.SectionLie.AffineSectionLie.Space A.scheme.hom η[A.scheme].left q) :
    Relative.TangentBaseChange.RelativeTangent.point (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) A.scheme.hom
        (Affine.SectionLie.AffineSectionLie.zeroPoint η[A.scheme].left q) (familyDifferential A q ρ a v) =
      Relative.TangentBaseChange.RelativeTangent.point (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) A.scheme.hom
        (Affine.SectionLie.AffineSectionLie.zeroPoint η[A.scheme].left q) v ≫ (ρ.map a).left :=
  Relative.TangentBaseChange.RelativeTangent.point_map (C := .of (DualNumber k)) (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k)
    A.scheme.hom (Affine.SectionLie.AffineSectionLie.zeroPoint η[A.scheme].left q)
    A.scheme.hom (Affine.SectionLie.AffineSectionLie.zeroPoint η[A.scheme].left q) (ρ.map a).left (𝟙 S)
    ((ρ.map a).w.trans (Category.comp_id A.scheme.hom).symm)
    (Section.AffineLieNaturality.AffineSectionLie.zeroPoint_comp η[A.scheme].left η[A.scheme].left q (ρ.map a).left
      (congrArg Over.Hom.left (IsMonHom.one_hom (ρ.map a)))) v

theorem action_pullback_projection (a : R) :
    ((ρ.pullback q).map a).left ≫ pullback.fst A.scheme.hom q =
      pullback.fst A.scheme.hom q ≫ (ρ.map a).left := by
  change ((Over.pullback q).map (ρ.map a)).left ≫ pullback.fst A.scheme.hom q = _
  exact pullback.lift_fst _ _ _

theorem fiberRelativeEquiv_map (a : R) (v : LiePoints.AlgebraicLie.Space (A.pullback q).scheme) :
    LieFiberEquivalence.AlgebraicLie.fiberRelativeEquiv A q (LieAlgebraic.AlgebraicLie.map ((ρ.pullback q).map a) v) =
      familyDifferential A q ρ a (LieFiberEquivalence.AlgebraicLie.fiberRelativeEquiv A q v) := by
  apply Relative.TangentBaseChange.RelativeTangent.point_injective (DualNumberReduction.AlgebraicLie.dualIdeal k) (DualNumberReduction.AlgebraicLie.dualIdeal_square k) A.scheme.hom
    (Affine.SectionLie.AffineSectionLie.zeroPoint η[A.scheme].left q)
  rw [LieFiberEquivalence.AlgebraicLie.fiberRelativeEquiv_point, familyDifferential_point, LieFiberEquivalence.AlgebraicLie.fiberRelativeEquiv_point]
  have h := congrArg (fun z : AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ (A.pullback q).scheme =>
    z.left ≫ pullback.fst A.scheme.hom q) (LieAlgebraic.AlgebraicLie.point_map ((ρ.pullback q).map a) v)
  refine h.trans ?_
  change ((LiePoints.AlgebraicLie.point (A.pullback q).scheme v).left ≫ ((ρ.pullback q).map a).left) ≫
    pullback.fst A.scheme.hom q = _
  rw [Category.assoc, action_pullback_projection, ← Category.assoc]

end AlgebraicLie

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LieFamilyDifferential
