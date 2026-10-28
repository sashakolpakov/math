import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.SectionPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniversalFrames

/-! # Level Pullback Faithful -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LevelPullbackFaithful

noncomputable section

/-! Full levels are detected by their labelled sections after an
epimorphic base change, without an invertibility or nonzero-level premise. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem fullLevel_pullback_injective_of_epi {S T : Scheme.{0}} {g N : ℕ}
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (u : T ⟶ S) [Epi u] :
    Function.Injective (fun α : A.FullLevel N => α.pullback u) := by
  intro α β h
  apply Iso.ext
  apply AbelianModuli.ReferenceFamily.UniversalFrames.LevelCover.torsionNatTrans_ext_on_constants
  intro c
  apply Subtype.ext
  apply Group.SectionPullback.groupSectionPullback_injective A.scheme u
  change Group.SectionPullback.groupSectionPullback A.scheme u (LevelSections.fullLevelSection α c) =
    Group.SectionPullback.groupSectionPullback A.scheme u (LevelSections.fullLevelSection β c)
  rw [Group.SectionPullback.fullLevelSection_pullback, Group.SectionPullback.fullLevelSection_pullback]
  exact congrArg (fun γ : (A.pullback u).FullLevel N => LevelSections.fullLevelSection γ c) h

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LevelPullbackFaithful
