import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.UniversalLevel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.Monomorphisms

/-! # Canonical Frame -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.CanonicalFrame.IntegralLevelCover

noncomputable section

/-! Full-level construction over arbitrary bases where the level is invertible.
Adapted from the corresponding proved ReferenceFamily construction; no characteristic-zero
hypothesis or supplied torsion trivialization is retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.Monomorphisms.LevelCover

variable {S : Scheme.{0}} {g N : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (hN : ∀ x : S, IsUnit (N : S.presheaf.stalk x))

def fullFrameInclusion [NeZero N] : FrameLocus.IntegralLevelCover.fullFrameScheme A hN (N := N) ⟶ AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N :=
  Over.homMk (FrameLocus.IntegralLevelCover.fullFrameOpen A hN).ι rfl

/-- The original coefficient map at the full-frame inclusion is
invertible, independently of the constructed presentation used to prove
existence of a level there. -/
theorem fullFrameLevelMap_isIso [NeZero N] :
    IsIso (AbelianModuli.ReferenceFamily.UniversalFrames.LevelCover.frameLevelMap A (FrameLocus.IntegralLevelCover.fullFrameScheme A hN) (fullFrameInclusion A hN (N := N))) :=
  AbelianModuli.ReferenceFamily.Finite.Monomorphisms.LevelCover.frameLevelMap_isIso_of_relative_split A _ _ (UniversalLevel.IntegralLevelCover.universalFullLevel A hN)

/-- The canonical universal level is the original coefficient map. -/
def canonicalFullFrameLevel [NeZero N] :
    (A.pullback (FrameLocus.IntegralLevelCover.fullFrameScheme A hN (N := N)).hom).FullLevel N := by
  let : IsIso (AbelianModuli.ReferenceFamily.UniversalFrames.LevelCover.frameLevelMap A (FrameLocus.IntegralLevelCover.fullFrameScheme A hN) (fullFrameInclusion A hN (N := N))) :=
    fullFrameLevelMap_isIso A hN
  exact asIso (AbelianModuli.ReferenceFamily.UniversalFrames.LevelCover.frameLevelMap A _ (fullFrameInclusion A hN))

theorem canonicalFullFrameLevel_classifying [NeZero N] :
    AbelianModuli.ReferenceFamily.IndependentFrames.LevelCover.frameOfRelativeLevel A (FrameLocus.IntegralLevelCover.fullFrameScheme A hN) (canonicalFullFrameLevel A hN (N := N)) =
      fullFrameInclusion A hN :=
  (AbelianModuli.ReferenceFamily.IndependentFrames.LevelCover.relativeFramePointsEquiv A _).left_inv _

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.CanonicalFrame.IntegralLevelCover
