import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.PullbackRecoveryIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.Reembedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

/-! # Pullback Reembedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Reembedding an inverse-image ideal family through the canonical ambient pullback isomorphism recovers the actual categorical base-change family exactly. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S T : Scheme.{u}} {P : Over S} {Q : Over T}
variable (F : Closed.Families.FlatClosedFamily P) (p : Q.left ⟶ P.left) (f : T ⟶ S) (hp : IsPullback p Q.hom P.hom f)

local instance ClosedFamily.PullbackReembedding.familyCartesianAmbientClosed : IsClosedImmersion (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso p f hp).hom.left :=
  Grassmann.ProjectivePresentation.overIso_closedImmersion (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso p f hp)

theorem Closed.Families.FlatClosedFamily.pullbackAlong_reembedIso :
    (F.pullbackAlong p f hp).reembed (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso p f hp).hom = F.baseChange f := by
  have : IsIso (F.pullbackAlongIso p f hp).hom.left :=
    inferInstanceAs (IsIso ((Over.forget T).map (F.pullbackAlongIso p f hp).hom))
  apply Closed.Families.FlatClosedFamily.ext
  change ((F.pullbackAlong p f hp).inclusion.left ≫ (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso p f hp).hom.left).ker =
    F.ideal.comap (pullback.fst P.hom f)
  have he := congrArg Over.Hom.left (F.pullbackAlongIso_inclusion p f hp)
  change (F.pullbackAlongIso p f hp).hom.left ≫ ((Over.pullback f).map F.inclusion).left =
    (F.pullbackAlong p f hp).inclusion.left ≫ (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso p f hp).hom.left at he
  rw [← he, Scheme.Hom.ker_comp_of_isIso]
  have hk := Graph.FamilyBaseChange.closedImmersion_ker_baseChange (Graph.FamilyBaseChange.overPullback_map_isPullback_flip f F.inclusion)
  change ((Over.pullback f).map F.inclusion).left.ker = F.ideal.comap (pullback.fst P.hom f)
  exact hk.trans (congrArg (fun I => I.comap (pullback.fst P.hom f)) F.ideal.ker_subschemeι)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
