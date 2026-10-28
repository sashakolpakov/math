import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.PullbackComposition

/-! # Restriction Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.RestrictionComposition

noncomputable section

/-! The product obtained by inserting a pulled-back line section respects composition of restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionPullback
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Transport OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.PullbackComposition

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  {M N P : Z.Modules} (hM : Line.Bundles.IsLine M) (hN : Line.Bundles.IsLine N)
  (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap M N P) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pullback g).obj M)

/-- Restricting the contracted formula twice agrees with inserting the same section after the
single composite restriction, with all actual fiber comparisons included. -/
theorem contraction_comp :
    (Scheme.Modules.pullback f).map (Contraction.contractLeft (BilinearPullback.pullback g hM hN β) s) ≫
        ((Scheme.Modules.pullbackComp f g).app P).hom =
      ((Scheme.Modules.pullbackComp f g).app N).hom ≫
        Contraction.contractLeft (BilinearPullback.pullback (f ≫ g) hM hN β)
          (ContractionPullback.pulledSection f s ≫ ((Scheme.Modules.pullbackComp f g).app M).hom) := by
  have hp := Transport.contractLeft_pullback_transport f (hM.pullback g) (hN.pullback g)
    (BilinearPullback.pullback g hM hN β) ((Scheme.Modules.pullbackComp f g).app M)
    ((Scheme.Modules.pullbackComp f g).app N) ((Scheme.Modules.pullbackComp f g).app P) s
  rw [PullbackComposition.pullback_comp f g hM hN β] at hp
  have hh := congrArg (fun t => ((Scheme.Modules.pullbackComp f g).app N).hom ≫ t) hp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hh.symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.RestrictionComposition
