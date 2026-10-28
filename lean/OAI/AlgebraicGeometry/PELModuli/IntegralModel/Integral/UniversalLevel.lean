import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.SpanningBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniversalLevel

/-! # Universal Level -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.UniversalLevel.IntegralLevelCover

noncomputable section

/-! Full-level construction over arbitrary bases where the level is invertible.
Adapted from the corresponding proved ReferenceFamily construction; no characteristic-zero
hypothesis or supplied torsion trivialization is retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniversalLevel.LevelCover

variable {S : Scheme.{0}} {g N : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (hN : ∀ x : S, IsUnit (N : S.presheaf.stalk x))

/-- The restricted universal coefficient map is an actual group-scheme
isomorphism, with the canonical pullback group structures. -/
def universalFrameGroupIso [NeZero N] :
    Grp.mk ((Over.pullback (FrameLocus.IntegralLevelCover.fullFrameOpen A hN (N := N)).ι).obj
      (AbelianModuli.HilbertConstruction.Level.Scheme.constantFullLevelScheme g N (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).left)) ≅
    Grp.mk ((Over.pullback (FrameLocus.IntegralLevelCover.fullFrameOpen A hN (N := N)).ι).obj
      ((A.pullback (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N)) := by
  let u := (FrameLocus.IntegralLevelCover.fullFrameOpen A hN (N := N)).ι
  let m := (Over.pullback u).map (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N) (𝟙 _))
  let : IsIso m := SpanningBaseChange.IntegralLevelCover.universalFrame_overPullback_isIso A hN
  let : IsMonHom m :=
    ((Over.pullback u).mapGrp.map (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameGroupSchemeMap A (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N) (𝟙 _))).hom.isMonHom_hom
  exact Grp.mkIso' (asIso m)

/-- The constructed universal full level on the actual full-frame
scheme, transported through the canonical iterated-pullback comparison. -/
def universalFullLevel [NeZero N] :
    (A.pullback (FrameLocus.IntegralLevelCover.fullFrameScheme A hN (N := N)).hom).FullLevel N := by
  let u := (FrameLocus.IntegralLevelCover.fullFrameOpen A hN (N := N)).ι
  let e := A.pullbackCompIso (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom u
  let : IsMonHom e.symm.hom := A.pullbackCompIso_symm_preservesGroup _ _
  exact (AbelianModuli.ReferenceFamily.UniversalLevel.LevelCover.levelOfPullbackGroupIso (A.pullback (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom)
    (FrameLocus.IntegralLevelCover.fullFrameOpen A hN).ι (universalFrameGroupIso A hN)).transport
      (B := A.pullback (u ≫ (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom)) e.symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.UniversalLevel.IntegralLevelCover
