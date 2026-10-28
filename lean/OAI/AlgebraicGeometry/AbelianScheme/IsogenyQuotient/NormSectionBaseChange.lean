import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramedNormSection
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PullbackSectionSquares
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionBaseChange

/-! # Norm Section Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormSectionBaseChange.Construction

noncomputable section

/-! The actual framed norm section respects affine base change through
the canonical line and tensor-power pullback comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionBaseChange

universe u v

theorem framedNormSection_baseChange
    {X Y X' Y' : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine X'] [IsAffine Y']
    (f : X ⟶ Y) (g : X' ⟶ Y') (j : X' ⟶ X) (i : Y' ⟶ Y)
    (hs : IsPullback j g f i) {ι : Type v} [Fintype ι]
    (b : letI := f.appTop.hom.toAlgebra; Module.Basis ι Γ(Y, ⊤) Γ(X, ⊤))
    {L : Y.Modules} (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L) [IsIso e] (d : ℕ)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj L) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i (FramedNormSection.Construction.framedNormSection f e d z) ≫ AbelianModuli.HilbertConstruction.Power.PullbackComparison.powerPullbackComparison i L d =
      FramedNormSection.Construction.framedNormSection g (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i e) d
        (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j z ≫ (PullbackSectionSquares.Construction.sectionPullbackSquareIso f g j i hs.w L).hom) := by
  have hcomp : IsIso (AbelianModuli.HilbertConstruction.Power.PullbackComparison.powerPullbackComparison i L d) :=
    AbelianModuli.HilbertConstruction.LineBundle.PowerBaseChange.powerPullbackComparison_isIso_of_trivial i (asIso e).symm d
  let c := asIso (AbelianModuli.HilbertConstruction.Power.PullbackComparison.powerPullbackComparison i L d)
  have he := AbelianModuli.HilbertConstruction.Power.SectionBaseChange.powerPullbackComparison_section i e d
  have hleft :
      AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i e) d)
        (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i (FramedNormSection.Construction.framedNormSection f e d z) ≫ c.hom) =
      i.appTop (Quotients.FiniteDescent.SchemeNorm.Construction.SchemeNormOpen.norm f (AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f e) z)) := by
    exact ((AbelianModuli.HilbertConstruction.Frame.FrameRestriction.frameCoordinate_congr he rfl).symm.trans
      (AbelianModuli.HilbertConstruction.Frame.FrameRestriction.frameCoordinate_targetIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection e d))
        (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i (FramedNormSection.Construction.framedNormSection f e d z)) c)).trans
      ((AbelianModuli.HilbertConstruction.Scalar.BaseChange.frameCoordinate_baseChange i (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection e d) (FramedNormSection.Construction.framedNormSection f e d z)).trans
        (congrArg i.appTop (FramedNormSection.Construction.framedNormSection_coordinate f e d z)))
  have hsource :
      AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection g (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i e))
        (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j z ≫ (PullbackSectionSquares.Construction.sectionPullbackSquareIso f g j i hs.w L).hom) =
      j.appTop (AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f e) z) := by
    exact ((AbelianModuli.HilbertConstruction.Frame.FrameRestriction.frameCoordinate_congr (PullbackSectionSquares.Construction.sectionPullbackSquareIso_section f g j i hs.w e) rfl).symm.trans
      (AbelianModuli.HilbertConstruction.Frame.FrameRestriction.frameCoordinate_targetIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f e)) (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j z)
        (PullbackSectionSquares.Construction.sectionPullbackSquareIso f g j i hs.w L))).trans
      (AbelianModuli.HilbertConstruction.Scalar.BaseChange.frameCoordinate_baseChange j (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f e) z)
  apply AbelianModuli.HilbertConstruction.Framed.AffineAnnihilation.frameCoordinate_injective (AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerSection (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i e) d)
  dsimp only
  exact hleft.trans ((NormBaseChange.Construction.schemeNorm_baseChange f g j i hs b _).symm.trans
    ((congrArg (Quotients.FiniteDescent.SchemeNorm.Construction.SchemeNormOpen.norm g) hsource).symm.trans
      (FramedNormSection.Construction.framedNormSection_coordinate g (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i e) d _).symm))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormSectionBaseChange.Construction
