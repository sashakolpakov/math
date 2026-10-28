import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.PowerFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapPullbackCongruence

/-! # Bundle Frame Map Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BundleFrameMapTransport

noncomputable section

/-! Pullback of a module isomorphism written as the comparison of two bundle frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

theorem frameMap_pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) (L M : Line.Bundles.LineBundle Z)
    (e : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj L.sheaf)
    (d : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj M.sheaf) :
    Module.MapPullbackComposition.moduleMapPullbackComp f g (e.symm ≪≫ d).hom =
      ((Relative.PowerFrames.compositeBundleFrame f g L e).symm ≪≫ Relative.PowerFrames.compositeBundleFrame f g M d).hom := by
  apply (cancel_epi (Relative.PowerFrames.compositeBundleFrame f g L e).hom).mp
  change (Ample.LineBundles.pullbackSection f e.hom ≫ ((Scheme.Modules.pullbackComp f g).app L.sheaf).hom) ≫
      (((Scheme.Modules.pullbackComp f g).app L.sheaf).inv ≫
        (Scheme.Modules.pullback f).map (e.inv ≫ d.hom) ≫
        ((Scheme.Modules.pullbackComp f g).app M.sheaf).hom) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, ← Power.SectionTransitions.pullbackSection_postcomp]
  rw [Iso.hom_inv_id_assoc]
  exact ((Relative.PowerFrames.compositeBundleFrame f g L e).hom_inv_id_assoc (Relative.PowerFrames.compositeBundleFrame f g M d).hom).symm

theorem frameMap_pullbackCongr {f g : X ⟶ Y} (h : f = g) (L M : Line.Bundles.LineBundle Y)
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L.sheaf)
    (d : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj M.sheaf) :
    Module.MapPullbackCongruence.moduleMapPullbackCongr h (e.symm ≪≫ d).hom =
      ((e ≪≫ (Scheme.Modules.pullbackCongr h).app L.sheaf).symm ≪≫
        (d ≪≫ (Scheme.Modules.pullbackCongr h).app M.sheaf)).hom := by
  subst g
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BundleFrameMapTransport
