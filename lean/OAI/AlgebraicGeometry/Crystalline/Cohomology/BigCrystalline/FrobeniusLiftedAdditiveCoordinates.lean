import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusAdditiveCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusLiftedCoordinates

/-! # Frobenius Lifted Additive Coordinates -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusLiftedAdditiveCoordinates.BigCrystallineFrobeniusLiftedAdditiveCoordinates

noncomputable section

/-! # Relative additive coordinates of the original lifted frame Frobenius -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) (hp : p.Prime) (W A σ : Type u) [CommRing W] [CommRing A]
  (hA : (p : A) = 0) (J : Ideal W) (δ : DividedPowers J)
  (base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))
  (e : W ≃+* W) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
  (h : Spec.map (CommRingCat.ofHom (Picard.Homomorphisms.Frobenius.Construction.powerRingHom p hp A hA)) ≫ base =
    base ≫ Spec.map (CommRingCat.ofHom e.toRingHom))
  (a : σ → A) [Fintype σ] [LinearOrder σ]

local notation "φ" => OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p hp A hA
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base
local notation "tw" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e he h
local notation "geo" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackLifts.BigCrystallinePullbackLifts.postcompose p W A A J δ base φ
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a

theorem coordinates (j : ℕ) (Q : C) (f : (geo).obj ((tw).obj Q) ⟶ Q)
    (z : ((K).X j).obj (op Q)) :
    TwistCoordinateForms.BigCrystallineTwistCoordinateForms.targetMap p W A J δ base a (op Q) j
      (FrobeniusTransport.BigCrystallineFrobeniusRawTransport.map p hp W A σ hA J δ base e he h a j Q f (ULift.up z)).down =
      FrobeniusAdditiveCoordinates.BigCrystallineFrobeniusAdditiveCoordinates.power p hp W A σ hA J δ base e he h a j Q
        (FrobeniusAdditiveCoordinates.BigCrystallineFrobeniusAdditiveCoordinates.ambient p hp W A σ hA J δ base e he h a j Q f
          (TwistCoordinateForms.BigCrystallineTwistCoordinateForms.targetMap p W A J δ base a (op Q) j z)) := by
  have hd := FrobeniusLiftedCoordinates.BigCrystallineFrobeniusLiftedCoordinates.map_down p hp W A σ hA J δ base e he h a j Q f z
  have hc := FrobeniusAdditiveCoordinates.BigCrystallineFrobeniusAdditiveCoordinates.coordinates p hp W A σ hA J δ base e he h a j Q f z
  exact (congrArg (TwistCoordinateForms.BigCrystallineTwistCoordinateForms.targetMap p W A J δ base a (op Q) j) hd).trans hc

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusLiftedAdditiveCoordinates.BigCrystallineFrobeniusLiftedAdditiveCoordinates
