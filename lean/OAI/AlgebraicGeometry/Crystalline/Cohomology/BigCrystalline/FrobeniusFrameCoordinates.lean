import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistCoordinateForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.AffineFrobeniusCoordinateForms

/-! # Frobenius Frame Coordinates -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusFrameCoordinates.BigCrystallineFrobeniusFrameCoordinates

noncomputable section

/-! # Relative-form coordinates of the original three frame transports -/

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
local notation "bF" => Spec.map (CommRingCat.ofHom φ) ≫ base
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base
local notation "tw" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e he h
local notation "geo" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PullbackLifts.BigCrystallinePullbackLifts.postcompose p W A A J δ base φ
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a

def transport (j : ℕ) (Q : C) (f : (geo).obj ((tw).obj Q) ⟶ Q)
    (z : ((K).X j).obj (op Q)) : ((K).X j).obj (op Q) :=
  TwistCoordinateForms.BigCrystallineTwistCoordinateForms.twistMap p W A J δ base bF e he h a (op Q) j
    (((AffineFrobeniusFrames.BigCrystallineAffineFrobeniusFrames.complexMap p hp W A σ hA J δ base a).f j).app
      (op ((tw).obj Q)) (((K).X j).map f.op z))

theorem transport_apply (j : ℕ) (Q : C) (f : (geo).obj ((tw).obj Q) ⟶ Q)
    (z : ((K).X j).obj (op Q)) :
    transport p hp W A σ hA J δ base e he h a j Q f z =
      TwistCoordinateForms.BigCrystallineTwistCoordinateForms.twistMap p W A J δ base bF e he h a (op Q) j
        (((AffineFrobeniusFrames.BigCrystallineAffineFrobeniusFrames.complexMap p hp W A σ hA J δ base a).f j).app
          (op ((tw).obj Q)) (((K).X j).map f.op z)) := rfl

theorem coordinates (j : ℕ) (Q : C) (f : (geo).obj ((tw).obj Q) ⟶ Q)
    (z : ((K).X j).obj (op Q)) :
    TwistCoordinateForms.BigCrystallineTwistCoordinateForms.targetMap p W A J δ base a (op Q) j
      (transport p hp W A σ hA J δ base e he h a j Q f z) =
    (PowerForms.BigCrystallinePowerForms.component a p (op ((tw).obj Q))).f j
      ((RelativeForms.BigCrystallineRelativeForms.map a f.op).f j
        (TwistCoordinateForms.BigCrystallineTwistCoordinateForms.targetMap p W A J δ base a (op Q) j z)) := by
  let y := ((K).X j).map f.op z
  let y' := ((AffineFrobeniusFrames.BigCrystallineAffineFrobeniusFrames.complexMap p hp W A σ hA J δ base a).f j).app
    (op ((tw).obj Q)) y
  have ht := TwistCoordinateForms.BigCrystallineTwistCoordinateForms.coordinates p W A J δ base bF e he h a (op Q) j y'
  have hg := AffineFrobeniusCoordinateForms.BigCrystallineAffineFrobeniusCoordinateForms.coordinates p hp W A σ hA J δ base a
    (op ((tw).obj Q)) j y
  have hm := FrameCoordinateSquares.BigCrystallineFrameCoordinateSquares.restriction p W A J δ base a f.op j z
  have hgm := hg.trans (congrArg (fun ω => (PowerForms.BigCrystallinePowerForms.component a p (op ((tw).obj Q))).f j ω) hm)
  have hfinal := ht.trans hgm
  convert hfinal using 1
  simp only [transport, TwistCoordinateForms.BigCrystallineTwistCoordinateForms.targetMap, y', y]
  rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusFrameCoordinates.BigCrystallineFrobeniusFrameCoordinates
