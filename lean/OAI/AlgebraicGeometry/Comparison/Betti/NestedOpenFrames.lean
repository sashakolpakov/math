import OAI.AlgebraicGeometry.Comparison.Betti.Open.UnitFrame
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Dual

/-! # Nested Open Frames -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.NestedOpenFrames.Dolbeault

noncomputable section

/-! Successive restrictions of an actual open frame agree with direct
restriction on the native poset of opens. -/

open _root_.CategoryTheory _root_.TopologicalSpace

variable {Z : TopCat.{0}} (R : TopCat.Sheaf RingCat.{0} Z) (M : SheafOfModules.{0} R)

theorem restrictOpenFrame_trans {U V W : Opens Z} (hVU : V ≤ U) (hWV : W ≤ V)
    (e : M.over U ≅ SheafOfModules.unit (R.over U)) :
    SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization R M V
        (SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization R M U e (Over.mk (homOfLE hVU)))
        (Over.mk (homOfLE hWV)) =
      SheafCohomology.Projective.Dual.SheafOfModules.restrictOverTrivialization R M U e
        (Over.mk (homOfLE (hWV.trans hVU))) := by
  apply Iso.ext
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro A
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.NestedOpenFrames.Dolbeault
