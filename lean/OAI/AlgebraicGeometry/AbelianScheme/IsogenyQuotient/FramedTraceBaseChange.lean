import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramedTraceSection
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PullbackSectionSquares

/-! # Framed Trace Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramedTraceBaseChange.Construction

noncomputable section

/-! The trace of a line-bundle section respects an arbitrary affine
Cartesian square through the actual pullback comparison isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem framedTraceSection_baseChange
    {X Y X' Y' : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine X'] [IsAffine Y']
    (f : X ⟶ Y) (g : X' ⟶ Y') (j : X' ⟶ X) (i : Y' ⟶ Y)
    (hs : IsPullback j g f i) {ι : Type v} [Fintype ι]
    (b : letI := f.appTop.hom.toAlgebra; Module.Basis ι Γ(Y, ⊤) Γ(X, ⊤))
    {L : Y.Modules} (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L) [IsIso e]
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback f).obj L) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i (FramedTraceSection.Construction.framedTraceSection f e z) =
      FramedTraceSection.Construction.framedTraceSection g (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i e)
        (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j z ≫ (PullbackSectionSquares.Construction.sectionPullbackSquareIso f g j i hs.w L).hom) := by
  have hsource :
      AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection g (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i e))
        (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j z ≫ (PullbackSectionSquares.Construction.sectionPullbackSquareIso f g j i hs.w L).hom) =
      j.appTop (AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f e) z) := by
    exact ((AbelianModuli.HilbertConstruction.Frame.FrameRestriction.frameCoordinate_congr (PullbackSectionSquares.Construction.sectionPullbackSquareIso_section f g j i hs.w e) rfl).symm.trans
      (AbelianModuli.HilbertConstruction.Frame.FrameRestriction.frameCoordinate_targetIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f e)) (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection j z)
        (PullbackSectionSquares.Construction.sectionPullbackSquareIso f g j i hs.w L))).trans
      (AbelianModuli.HilbertConstruction.Scalar.BaseChange.frameCoordinate_baseChange j (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection f e) z)
  apply AbelianModuli.HilbertConstruction.Framed.AffineAnnihilation.frameCoordinate_injective (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection i e)
  dsimp only
  rw [AbelianModuli.HilbertConstruction.Scalar.BaseChange.frameCoordinate_baseChange, FramedTraceSection.Construction.framedTraceSection_coordinate,
    FramedTraceSection.Construction.framedTraceSection_coordinate, hsource, Trace.Construction.schemeTrace_baseChange f g j i hs b]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramedTraceBaseChange.Construction
