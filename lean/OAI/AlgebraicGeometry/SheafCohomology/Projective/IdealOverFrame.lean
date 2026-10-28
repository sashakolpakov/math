/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OverGenerator
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CanonicalIdealFrame

/-! # Ideal Over Frame -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.IdealOverFrame

noncomputable section

/-! In canonical local frames the kernel inclusion is its defining equation. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

theorem localIdealGeneratorOverTrivialization_inv_comp
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (U : Y.affineOpens) (r : Γ(Y, U.1)) (hr : r ∈ f.ker.ideal U)
    (hspan : f.ker.ideal U = Ideal.span {r})
    (hnzd : r ∈ nonZeroDivisors Γ(Y, U.1)) :
    let eGen := CanonicalIdealFrame.localIdealGeneratorIso f U r hr hspan hnzd
    let eOver := Invertible.Scheme.Modules.overTrivializationOfRestrictIso
      (IdealModule.idealModule f) U.1 eGen.symm
    eOver.inv ≫ (IdealModule.idealModuleToUnit f).over U.1 =
      Dual.SheafOfModules.overUnitScalarEnd Y.ringCatSheaf U.1 r := by
  dsimp only
  rw [OverGenerator.overTrivialization_inv_eq_overGenerator (IdealModule.idealModule f) U.1
    (CanonicalIdealFrame.localIdealElement f U r hr) (CanonicalIdealFrame.localIdealGeneratorIso f U r hr hspan hnzd) rfl]
  rw [OverGenerator.overGeneratorHom_comp]
  have hs : (IdealModule.idealModuleToUnit f).val.app (op U.1)
      (CanonicalIdealFrame.localIdealElement f U r hr) = r := by
    rw [← IdealModule.idealModuleAppIdealIso_coe, CanonicalIdealFrame.idealModuleAppIdealIso_hom_localIdealElement]
  rw [hs]
  rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.IdealOverFrame
