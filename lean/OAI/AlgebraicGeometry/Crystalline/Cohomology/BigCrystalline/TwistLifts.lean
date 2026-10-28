import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameMaps
import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist

/-! # Twist Lifts -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistLifts.BigCrystallineTwistLifts

noncomputable section

/-! # Original frame coordinates under the actual crystalline base twist -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts

universe u

variable (p : ℕ) (W A σ : Type u) [CommRing W] [CommRing A]
  (J : Ideal W) (δ : DividedPowers J)
  (base base' : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))
  (e : W ≃+* W) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
  (h : base' = base ≫ Spec.map (CommRingCat.ofHom e.toRingHom)) (a : σ → A)

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base
local notation "ι" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e he h

theorem residual (Q : C) :
    FrameLifts.BigCrystallineFrameLifts.residualMap p W A J δ base' ((ι).obj Q) =
      FrameLifts.BigCrystallineFrameLifts.residualMap p W A J δ base Q := rfl

theorem lift (Q : C) (i : σ) :
    FrameLifts.BigCrystallineFrameLifts.lift p W A σ J δ base' a ((ι).obj Q) i =
      FrameLifts.BigCrystallineFrameLifts.lift p W A σ J δ base a Q i := rfl

theorem translation {Q P : C} (f : Q ⟶ P) (i : σ) :
    FrameLifts.BigCrystallineFrameLifts.translation a ((ι).map f) i =
      FrameLifts.BigCrystallineFrameLifts.translation a f i := rfl

theorem ambientMap {Q P : C} (f : Q ⟶ P) :
    (FrameMaps.BigCrystallineFrameMaps.ambientMap a ((ι).map f)).toRingHom =
      (FrameMaps.BigCrystallineFrameMaps.ambientMap a f).toRingHom := rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistLifts.BigCrystallineTwistLifts
