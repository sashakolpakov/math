import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.FrameLocus
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SpanningBaseChange

/-! # Spanning Base Change -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.SpanningBaseChange.IntegralLevelCover

noncomputable section

/-! Full-level construction over arbitrary bases where the level is invertible.
Adapted from the corresponding proved ReferenceFamily construction; no characteristic-zero
hypothesis or supplied torsion trivialization is retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SpanningBaseChange.LevelCover

variable {S : Scheme.{0}} {g N : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (hN : ∀ x : S, IsUnit (N : S.presheaf.stalk x))

theorem universalFrame_overPullback_isIso [NeZero N] :
    IsIso ((Over.pullback (FrameLocus.IntegralLevelCover.fullFrameOpen A hN (N := N)).ι).map
      (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N) (𝟙 _))) := by
  have he := (TorsionDivision.torsionScheme_finite_etale (A.pullback (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom) N (fun x => by
      simpa only [map_natCast] using (hN ((AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom x)).map
        ((AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom.stalkMap x).hom)).2
  let : Etale ((A.pullback (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N).hom).torsionScheme N).hom := he
  let : IsOpenImmersion (AbelianModuli.ReferenceFamily.Frame.GroupScheme.LevelCover.frameSchemeMap A (AbelianModuli.ReferenceFamily.Level.Cover.LevelCover.frameScheme A N) (𝟙 _)).left :=
    FrameLocus.IntegralLevelCover.frameSchemeMap_open A _ _
  apply AbelianModuli.ReferenceFamily.SpanningBaseChange.LevelCover.overPullbackMap_isIso_of_spans
  intro y hy
  rw [Scheme.Opens.range_ι] at hy
  exact (FrameLocus.IntegralLevelCover.mem_fullFrameOpen_iff A hN _).mp hy y rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Integral.SpanningBaseChange.IntegralLevelCover
