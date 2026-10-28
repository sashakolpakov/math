import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusFrameCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.AdditiveEvaluation

/-! # Frobenius Additive Coordinates -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusAdditiveCoordinates.BigCrystallineFrobeniusAdditiveCoordinates

noncomputable section

/-! # Additive coordinates of the original three frame transports -/

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

def ambient (j : ℕ) (Q : C) (f : (geo).obj ((tw).obj Q) ⟶ Q) :
    (RelativeForms.BigCrystallineRelativeForms.object (σ := σ) (op Q)).X j →+
      (RelativeForms.BigCrystallineRelativeForms.object (σ := σ) (op ((geo).obj ((tw).obj Q)))).X j :=
  Module.AdditiveEvaluation.ModuleAdditiveEvaluation.map ((RelativeForms.BigCrystallineRelativeForms.map a f.op).f j)

def power (j : ℕ) (Q : C) :
    (RelativeForms.BigCrystallineRelativeForms.object (σ := σ) (op ((tw).obj Q))).X j →+
      (RelativeForms.BigCrystallineRelativeForms.object (σ := σ) (op ((tw).obj Q))).X j :=
  Module.AdditiveEvaluation.ModuleAdditiveEvaluation.map ((PowerForms.BigCrystallinePowerForms.component a p (op ((tw).obj Q))).f j)

theorem composition_apply (j : ℕ) (Q : C) (f : (geo).obj ((tw).obj Q) ⟶ Q)
    (z : ((K).X j).obj (op Q)) :
    power p hp W A σ hA J δ base e he h a j Q
      (ambient p hp W A σ hA J δ base e he h a j Q f
        (TwistCoordinateForms.BigCrystallineTwistCoordinateForms.targetMap p W A J δ base a (op Q) j z)) =
      (PowerForms.BigCrystallinePowerForms.component a p (op ((tw).obj Q))).f j
        ((RelativeForms.BigCrystallineRelativeForms.map a f.op).f j
          (TwistCoordinateForms.BigCrystallineTwistCoordinateForms.targetMap p W A J δ base a (op Q) j z)) :=
  Module.AdditiveEvaluation.ModuleAdditiveEvaluation.map_double_apply ((RelativeForms.BigCrystallineRelativeForms.map a f.op).f j)
    ((PowerForms.BigCrystallinePowerForms.component a p (op ((tw).obj Q))).f j)
    (TwistCoordinateForms.BigCrystallineTwistCoordinateForms.targetMap p W A J δ base a (op Q) j z)

theorem coordinates (j : ℕ) (Q : C) (f : (geo).obj ((tw).obj Q) ⟶ Q)
    (z : ((K).X j).obj (op Q)) :
    TwistCoordinateForms.BigCrystallineTwistCoordinateForms.targetMap p W A J δ base a (op Q) j
      (FrobeniusFrameCoordinates.BigCrystallineFrobeniusFrameCoordinates.transport p hp W A σ hA J δ base e he h a j Q f z) =
      power p hp W A σ hA J δ base e he h a j Q
        (ambient p hp W A σ hA J δ base e he h a j Q f
          (TwistCoordinateForms.BigCrystallineTwistCoordinateForms.targetMap p W A J δ base a (op Q) j z)) :=
  (FrobeniusFrameCoordinates.BigCrystallineFrobeniusFrameCoordinates.coordinates p hp W A σ hA J δ base e he h a j Q f z).trans
    (composition_apply p hp W A σ hA J δ base e he h a j Q f z).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusAdditiveCoordinates.BigCrystallineFrobeniusAdditiveCoordinates
