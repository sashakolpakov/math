import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramedNormSection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SectionTransitions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.ProductPullbacks

/-! # Norm Section Line Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormSectionLineIsomorphism.Construction

noncomputable section

/-! A genuine isomorphism of line sheaves carries the norm section
to the norm section in the transported frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem framedNormSection_mapIso {X Y : Scheme.{u}} (q : X ⟶ Y)
    {L M : Y.Modules} (e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ L) [IsIso e]
    (a : L ≅ M) (d : ℕ)
    (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ (Scheme.Modules.pullback q).obj L) :
    FramedNormSection.Construction.framedNormSection q (e ≫ a.hom) d (z ≫ (Scheme.Modules.pullback q).map a.hom) =
      FramedNormSection.Construction.framedNormSection q e d z ≫ AbelianModuli.HilbertConstruction.TensorPower.Maps.tensorPowerMap a.hom d := by
  have hc : AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection q (e ≫ a.hom))
      (z ≫ (Scheme.Modules.pullback q).map a.hom) =
      AbelianModuli.HilbertConstruction.Frame.Coordinates.frameCoordinate (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection q e) z :=
    (AbelianModuli.HilbertConstruction.Frame.FrameRestriction.frameCoordinate_congr (AbelianModuli.HilbertConstruction.Power.SectionTransitions.pullbackSection_postcomp q e a.hom) rfl).trans
      (AbelianModuli.HilbertConstruction.Frame.FrameRestriction.frameCoordinate_targetIso (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection q e) z ((Scheme.Modules.pullback q).mapIso a))
  unfold FramedNormSection.Construction.framedNormSection
  rw [hc]
  simp only [AbelianModuli.HilbertConstruction.Framed.PowerNumerators.framedPowerNumerator, AbelianModuli.HilbertConstruction.TensorPower.ProductPullbacks.tensorPowerSection_postcomp, Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormSectionLineIsomorphism.Construction
