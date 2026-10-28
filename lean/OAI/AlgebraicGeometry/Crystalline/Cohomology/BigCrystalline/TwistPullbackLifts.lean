import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackLifts
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistLifts

/-! # Twist Pullback Lifts -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistPullbackLifts.BigCrystallineTwistPullbackLifts

noncomputable section

/-! # Chosen lifts under a base twist followed by geometric pullback -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) (W A σ : Type u) [CommRing W] [CommRing A]
  (J : Ideal W) (δ : DividedPowers J)
  (base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))
  (e : W ≃+* W) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
  (φ : A →+* A)
  (h : Spec.map (CommRingCat.ofHom φ) ≫ base = base ≫ Spec.map (CommRingCat.ofHom e.toRingHom))
  (a : σ → A)

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base
local notation "T" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e he h
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.postcompose (Spec.map (CommRingCat.ofHom φ)) rfl

theorem lift (Q : C) (i : σ) :
    FrameLifts.BigCrystallineFrameLifts.lift p W A σ J δ base a ((T ⋙ U).obj Q) i =
      FrameLifts.BigCrystallineFrameLifts.lift p W A σ J δ base (φ ∘ a) Q i :=
  PullbackLifts.BigCrystallinePullbackLifts.lift p W A A σ J δ base φ a ((T).obj Q) i

theorem coordinate (Q : C) (i : σ) :
    (show DividedPowerAlgebra Q.ring (σ →₀ Q.ring) from
      FrameMaps.BigCrystallineFrameMaps.coordinate a ((T ⋙ U).obj Q) i) =
      FrameMaps.BigCrystallineFrameMaps.coordinate (φ ∘ a) Q i :=
  congrArg (fun x : Q.ring =>
    algebraMap Q.ring (DividedPowerAlgebra Q.ring (σ →₀ Q.ring)) x +
      Multivariable.DividedAlgebra.MultivariableDividedAlgebra.generator Q.ring σ 1 i)
    (lift p W A σ J δ base e he φ h a Q i)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistPullbackLifts.BigCrystallineTwistPullbackLifts
