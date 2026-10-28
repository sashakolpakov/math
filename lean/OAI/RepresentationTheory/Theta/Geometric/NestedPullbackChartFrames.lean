import OAI.RepresentationTheory.Theta.Geometric.OpenFramesFactored
import OAI.RepresentationTheory.Theta.Geometric.Pullback.SquareFrames

/-! # Nested Pullback Chart Frames -/

namespace OAI.RepresentationTheory.Theta.Geometric.NestedPullbackChartFrames

noncomputable section

/-! Compatibility of pulled-back chart frames with nested algebraic opens. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem pullbackChartFrame_nested {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    {U V : Y.Opens} (h : V ≤ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj U.toScheme) :
    (Scheme.Modules.pullbackCongr (X.homOfLE_ι (f.preimage_mono h)).symm).app ((Scheme.Modules.pullback f).obj M) ≪≫
      FactoredPullbackFrames.factoredPullbackFrame (X.homOfLE (f.preimage_mono h)) (f ⁻¹ᵁ U).ι (OpenFramesFactored.pullbackChartFrame f M U e) =
    OpenFramesFactored.pullbackChartFrame f M V
      ((Scheme.Modules.pullbackCongr (Y.homOfLE_ι h).symm).app M ≪≫
        FactoredPullbackFrames.factoredPullbackFrame (Y.homOfLE h) U.ι e) := by
  exact Pullback.SquareFrames.pullbackSquareFrame_nested f (f ⁻¹ᵁ U).ι (f ⁻¹ᵁ V).ι U.ι V.ι
    (X.homOfLE (f.preimage_mono h)) (Y.homOfLE h) (f ∣_ U) (f ∣_ V)
    (X.homOfLE_ι (f.preimage_mono h)) (Y.homOfLE_ι h)
    (morphismRestrict_ι f U) (morphismRestrict_ι f V) (morphismRestrict_homOfLE f V U h) M e

end

end OAI.RepresentationTheory.Theta.Geometric.NestedPullbackChartFrames
