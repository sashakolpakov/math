import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Group.SectionPullback
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LevelMapPullback

/-! # Level From Local Sections -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LevelFromLocalSections

noncomputable section

/-! Construct an actual full level from actual global sections which
recover a given full level on an fppf base cover. No inverse level or
effectivity assumption is supplied: the inverse follows from sheaf descent. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {g N : ℕ} {S T : Scheme.{0}} (u : T ⟶ S)
    [Flat u] [Surjective u] [LocallyOfFinitePresentation u]
    (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (β : (A.pullback u).FullLevel N)
    (z : Multiplicative (Fin (2 * g) → ZMod N) → (Over.mk (𝟙 S) ⟶ A.scheme))
    (hz : ∀ c, Group.SectionPullback.groupSectionPullback A.scheme u (z c) = LevelSections.fullLevelSection β c)

def fullLevelOfLocalSectionsMap :
    AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.constantLevelFunctor g N S ⟶ A.torsionFunctor N :=
  AbelianModuli.ReferenceFamily.UniversalFrames.LevelCover.torsionSectionExtension A (Group.SectionPullback.torsionSectionsOfPullback u A β z hz)

theorem fullLevelOfLocalSectionsMap_const (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    ((fullLevelOfLocalSectionsMap u A β z hz).app (.op (Over.mk (𝟙 S)))
      (LocallyConstant.const S c)).val = z c :=
  congrArg Subtype.val (AbelianModuli.ReferenceFamily.UniversalFrames.LevelCover.torsionSectionExtension_const A
    (Group.SectionPullback.torsionSectionsOfPullback u A β z hz) c)

theorem fullLevelOfLocalSectionsMap_pullback :
    LevelMapPullback.fullLevelMapPullback A u (fullLevelOfLocalSectionsMap u A β z hz) = β.hom := by
  apply LevelMapPullback.fullLevelMapPullback_eq A u
  intro c
  rw [fullLevelOfLocalSectionsMap_const]
  exact (Group.SectionPullback.groupSectionPullback_fst A.scheme u (z c)).symm.trans
    (congrArg (fun t => t.left ≫ pullback.fst A.scheme.hom u) (hz c))

instance fullLevelOfLocalSectionsMap_isIso : IsIso (fullLevelOfLocalSectionsMap u A β z hz) := by
  have : IsIso (LevelMapPullback.fullLevelMapPullback A u (fullLevelOfLocalSectionsMap u A β z hz)) := by
    rw [fullLevelOfLocalSectionsMap_pullback]
    infer_instance
  exact LevelMapPullback.fullLevelMap_isIso_of_pullback A u _

def fullLevelOfLocalSections : A.FullLevel N := asIso (fullLevelOfLocalSectionsMap u A β z hz)

theorem fullLevelOfLocalSections_section (c : Multiplicative (Fin (2 * g) → ZMod N)) :
    LevelSections.fullLevelSection (fullLevelOfLocalSections u A β z hz) c = z c :=
  fullLevelOfLocalSectionsMap_const u A β z hz c

theorem fullLevelOfLocalSections_pullback :
    (fullLevelOfLocalSections u A β z hz).pullback u = β := by
  apply Iso.ext
  exact fullLevelOfLocalSectionsMap_pullback u A β z hz

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LevelFromLocalSections
