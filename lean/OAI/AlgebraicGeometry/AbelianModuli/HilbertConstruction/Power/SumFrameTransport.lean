import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SumFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.MapGluing

/-! # Sum Frame Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SumFrameTransport

noncomputable section

/-! The local power-addition comparison respects refinement of the trivializing open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

theorem localPowerSumIso_comp (f : X ⟶ Y) (g : Y ⟶ Z) (L : Line.Bundles.LineBundle Z)
    (e : Line.Bundles.structureModule Y ≅ (Scheme.Modules.pullback g).obj L.sheaf) (m n : ℕ) :
    Module.MapPullbackComposition.moduleMapPullbackComp f g (SumFrames.localPowerSumIso g L e m n).hom =
      (SumFrames.localPowerSumIso (f ≫ g) L (Relative.PowerFrames.compositeBundleFrame f g L e) m n).hom := by
  have hs : Relative.PowerFrames.compositeBundleFrame f g (L.tensorPower (m + n)) (Relative.PowerFrames.relativePowerFrame g L e (m + n)) =
      Relative.PowerFrames.relativePowerFrame (f ≫ g) L (Relative.PowerFrames.compositeBundleFrame f g L e) (m + n) :=
    Iso.ext (Relative.PowerFrames.relativePowerFrame_comp f g L e (m + n))
  have ht : Relative.PowerFrames.compositeBundleFrame f g ((L.tensorPower m).tensor (L.tensorPower n)) (SumFrames.powerSumFrame g L e m n) =
      SumFrames.powerSumFrame (f ≫ g) L (Relative.PowerFrames.compositeBundleFrame f g L e) m n :=
    Iso.ext (SumFrames.powerSumFrame_comp f g L e m n)
  have hc := BundleFrameMapTransport.frameMap_pullbackComp f g (L.tensorPower (m + n))
    ((L.tensorPower m).tensor (L.tensorPower n)) (Relative.PowerFrames.relativePowerFrame g L e (m + n))
    (SumFrames.powerSumFrame g L e m n)
  change Module.MapPullbackComposition.moduleMapPullbackComp f g (SumFrames.localPowerSumIso g L e m n).hom = _ at hc
  have hd : ((Relative.PowerFrames.compositeBundleFrame f g (L.tensorPower (m + n))
      (Relative.PowerFrames.relativePowerFrame g L e (m + n))).symm ≪≫
      Relative.PowerFrames.compositeBundleFrame f g ((L.tensorPower m).tensor (L.tensorPower n))
        (SumFrames.powerSumFrame g L e m n)).hom =
      (SumFrames.localPowerSumIso (f ≫ g) L (Relative.PowerFrames.compositeBundleFrame f g L e) m n).hom := by
    rw [hs, ht]
    rfl
  exact hc.trans hd

theorem localPowerSumIso_congr {f g : X ⟶ Y} (h : f = g) (L : Line.Bundles.LineBundle Y)
    (e : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback f).obj L.sheaf)
    (d : Line.Bundles.structureModule X ≅ (Scheme.Modules.pullback g).obj L.sheaf) (m n : ℕ) :
    Module.MapPullbackCongruence.moduleMapPullbackCongr h (SumFrames.localPowerSumIso f L e m n).hom = (SumFrames.localPowerSumIso g L d m n).hom := by
  subst g
  rw [Module.MapPullbackCongruence.moduleMapPullbackCongr_refl, SumFrames.localPowerSumIso_independent f L e d m n]

theorem localPowerSumIso_open_refine (L : Line.Bundles.LineBundle X) {U V : X.Opens} (h : U ≤ V)
    (e : Line.Bundles.structureModule V.toScheme ≅ (Scheme.Modules.pullback V.ι).obj L.sheaf)
    (d : Line.Bundles.structureModule U.toScheme ≅ (Scheme.Modules.pullback U.ι).obj L.sheaf) (m n : ℕ) :
    Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap h) (SumFrames.localPowerSumIso V.ι L e m n).hom =
      (SumFrames.localPowerSumIso U.ι L d m n).hom := by
  exact (congrArg (fun φ => Module.MapPullbackCongruence.moduleMapPullbackCongr (X.homOfLE_ι h) φ)
    (localPowerSumIso_comp (X.homOfLE h) V.ι L e m n)).trans
      (localPowerSumIso_congr (X.homOfLE_ι h) L (Relative.PowerFrames.compositeBundleFrame (X.homOfLE h) V.ι L e) d m n)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.SumFrameTransport
