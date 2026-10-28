import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusTransport
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusFrameCoordinates
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.TwistLiftEvaluation

/-! # Frobenius Lifted Coordinates -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusLiftedCoordinates.BigCrystallineFrobeniusLiftedCoordinates

noncomputable section

/-! # The original coefficient-lifted raw transport has the prescribed underlying frame map -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

universe u

private theorem lift_apply (W : Type u) [CommRing W] {M N : ModuleCat.{u} W}
    (f : M ⟶ N) (z : M) :
    ((FrameSheafResolution.BigCrystallineFrameSheafResolution.coefficientLift W).map f).hom (ULift.up z) =
      ULift.up (f.hom z) := rfl

variable (p : ℕ) (hp : p.Prime) (W A σ : Type u) [CommRing W] [CommRing A]
  (hA : (p : A) = 0) (J : Ideal W) (δ : DividedPowers J)
  (base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W))
  (e : W ≃+* W) (he : DividedPowers.IsDPMorphism δ δ e.toRingHom)
  (h : Spec.map (CommRingCat.ofHom (Picard.Homomorphisms.Frobenius.Construction.powerRingHom p hp A hA)) ≫ base =
    base ≫ Spec.map (CommRingCat.ofHom e.toRingHom))
  (a : σ → A) [Fintype σ] [LinearOrder σ]

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base
local notation "K" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := base) a

local notation "φ" => OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.powerRingHom p hp A hA
local notation "bF" => Spec.map (CommRingCat.ofHom φ) ≫ base
local notation "tw" => OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineBaseTwist.twist (p := p) e he h
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameResolution.BigCrystallineFrameResolution.complex (p := p) (J := J) (δ := δ) (base := bF) a

omit [LinearOrder σ] in
theorem restriction_apply (j : ℕ) (Q : C)
    (f : (FrobeniusTransport.BigCrystallineFrobeniusRawTransport.transformed p hp W A hA J δ base e he h).obj Q ⟶ Q)
    (z : ((K).X j).obj (op Q)) :
    (FrobeniusTransport.BigCrystallineFrobeniusRawTransport.restrictionHom p hp W A σ hA J δ base e he h a j Q f).hom
      (ULift.up z) = ULift.up (((K).X j).map f.op z) :=
  lift_apply W (((K).X j).map f.op) z

theorem geometric_apply (j : ℕ) (Q : C)
    (z : ((K).X j).obj (op ((FrobeniusTransport.BigCrystallineFrobeniusRawTransport.transformed p hp W A hA J δ base e he h).obj Q))) :
    (FrobeniusTransport.BigCrystallineFrobeniusRawTransport.geometricHom p hp W A σ hA J δ base e he h a j Q).hom
      (ULift.up z) = ULift.up
        (((AffineFrobeniusFrames.BigCrystallineAffineFrobeniusFrames.complexMap p hp W A σ hA J δ base a).f j).app (op ((tw).obj Q)) z) :=
  lift_apply W (((AffineFrobeniusFrames.BigCrystallineAffineFrobeniusFrames.complexMap p hp W A σ hA J δ base a).f j).app
    (op ((tw).obj Q))) z

theorem twist_apply (j : ℕ) (Q : C) (z : ((L).X j).obj (op ((tw).obj Q))) :
    ScalarRestricted.ScalarRestrictedAdditiveMap.map (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e).symm.toRingHom
      (FrobeniusTransport.BigCrystallineFrobeniusRawTransport.twistHom p hp W A σ hA J δ base e he h a j Q) (ULift.up z) =
    ULift.up (TwistCoordinateForms.BigCrystallineTwistCoordinateForms.twistMap p W A J δ base bF e he h a (op Q) j z) := by
  have ht := TwistLiftEvaluation.BigCrystallineTwistLiftEvaluation.apply p W A J δ base bF e he h ((L).X j) ((K).X j)
    ((TwistResolution.BigCrystallineTwistResolution.iso p W A J δ base bF e he h a).hom.f j) (op Q) z
  convert ht using 1
  simp only [FrobeniusTransport.BigCrystallineFrobeniusRawTransport.twistHom, TwistGeneratorCoordinates.BigCrystallineTwistGeneratorCoordinates.rawMap,
    TwistCoordinateForms.BigCrystallineTwistCoordinateForms.twistMap, TwistCoordinateForms.BigCrystallineTwistCoordinateForms.twistHom]
  rfl

theorem map_down (j : ℕ) (Q : C)
    (f : (FrobeniusTransport.BigCrystallineFrobeniusRawTransport.transformed p hp W A hA J δ base e he h).obj Q ⟶ Q)
    (z : ((K).X j).obj (op Q)) :
    (ULift.down : ULift.{u + 1} (((K).X j).obj (op Q)) → ((K).X j).obj (op Q))
      (FrobeniusTransport.BigCrystallineFrobeniusRawTransport.map p hp W A σ hA J δ base e he h a j Q f (ULift.up z)) =
      FrobeniusFrameCoordinates.BigCrystallineFrobeniusFrameCoordinates.transport p hp W A σ hA J δ base e he h a j Q f z := by
  let x₁ : ((K).X j).obj
      (op ((FrobeniusTransport.BigCrystallineFrobeniusRawTransport.transformed p hp W A hA J δ base e he h).obj Q)) :=
    ((K).X j).map f.op z
  let x₂ : ((L).X j).obj (op ((tw).obj Q)) :=
    ((AffineFrobeniusFrames.BigCrystallineAffineFrobeniusFrames.complexMap p hp W A σ hA J δ base a).f j).app (op ((tw).obj Q)) x₁
  let t : ((L).X j).obj (op ((tw).obj Q)) →+ ((K).X j).obj (op Q) :=
    TwistCoordinateForms.BigCrystallineTwistCoordinateForms.twistMap p W A J δ base bF e he h a (op Q) j
  have hm := FrobeniusTransport.BigCrystallineFrobeniusRawTransport.map_apply p hp W A σ hA J δ base e he h a j Q f (ULift.up z)
  have hr := restriction_apply p hp W A σ hA J δ base e he h a j Q f z
  have hg := geometric_apply p hp W A σ hA J δ base e he h a j Q x₁
  have ht := twist_apply p hp W A σ hA J δ base e he h a j Q x₂
  have hgm := (congrArg
    (FrobeniusTransport.BigCrystallineFrobeniusRawTransport.geometricHom p hp W A σ hA J δ base e he h a j Q).hom hr).trans hg
  have htm := (congrArg
    (ScalarRestricted.ScalarRestrictedAdditiveMap.map (NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology.coefficientEquiv e).symm.toRingHom
      (FrobeniusTransport.BigCrystallineFrobeniusRawTransport.twistHom p hp W A σ hA J δ base e he h a j Q)) hgm).trans ht
  have hfinal : FrobeniusTransport.BigCrystallineFrobeniusRawTransport.map p hp W A σ hA J δ base e he h a j Q f (ULift.up z) =
      ULift.up (t x₂) := hm.trans htm
  have hd := congrArg
    (ULift.down : ULift.{u + 1} (((K).X j).obj (op Q)) → ((K).X j).obj (op Q)) hfinal
  dsimp only [t, x₂, x₁] at hd
  convert hd using 1
  simp only [FrobeniusFrameCoordinates.BigCrystallineFrobeniusFrameCoordinates.transport]
  congr 1

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrobeniusLiftedCoordinates.BigCrystallineFrobeniusLiftedCoordinates
