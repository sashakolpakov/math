import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameMaps
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.PowerNaturality

/-! # Power Coordinates -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PowerCoordinates.BigCrystallinePowerCoordinates

noncomputable section

/-! # Power-coordinate maps for the original big crystalline frame lifts -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts

universe u

variable {p : ℕ} {W A σ : Type u} [CommRing W] [CommRing A]
  {J : Ideal W} {δ : DividedPowers J} {base : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of W)}
  (a : σ → A) (m : ℕ)

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W A J δ base

def targetLift (Q : C) : σ → Q.ring := FrameLifts.BigCrystallineFrameLifts.lift p W A σ J δ base a Q

def sourceLift (Q : C) : σ → Q.ring :=
  FrameLifts.BigCrystallineFrameLifts.lift p W A σ J δ base (fun i => a i ^ m) Q

theorem power_difference_mem (Q : C) (i : σ) : targetLift a Q i ^ m - sourceLift a m Q i ∈ Q.ideal := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mk Q.ideal
    (FrameLifts.BigCrystallineFrameLifts.lift p W A σ J δ base a Q i ^ m -
      FrameLifts.BigCrystallineFrameLifts.lift p W A σ J δ base (fun j => a j ^ m) Q i) = 0
  rw [map_sub, map_pow, FrameLifts.BigCrystallineFrameLifts.reduction_lift,
    FrameLifts.BigCrystallineFrameLifts.reduction_lift, map_pow, sub_self]

def map (Q : C) : DividedPowerAlgebra Q.ring (σ →₀ Q.ring) →ₐ[W]
    DividedPowerAlgebra Q.ring (σ →₀ Q.ring) :=
  (FreeRelative.PowerMap.FreeRelativePowerMap.map Q.ring σ Q.ideal Q.dividedPowers m
    (targetLift a Q) (sourceLift a m Q) (power_difference_mem a m Q)).restrictScalars W

theorem map_isDPMorphism (Q : C) : DividedPowers.IsDPMorphism
    (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.ring σ Q.ideal Q.dividedPowers)
    (FreeRelative.Powers.FreeRelativePowers.dividedPowers Q.ring σ Q.ideal Q.dividedPowers)
    (map a m Q).toRingHom :=
  FreeRelative.PowerMap.FreeRelativePowerMap.map_isDPMorphism Q.ring σ Q.ideal Q.dividedPowers m
    (targetLift a Q) (sourceLift a m Q) (power_difference_mem a m Q)

theorem map_total (Q : C) (i : σ) :
    map a m Q (FrameMaps.BigCrystallineFrameMaps.coordinate (fun j => a j ^ m) Q i) =
      FrameMaps.BigCrystallineFrameMaps.coordinate a Q i ^ m :=
  FreeRelative.PowerMap.FreeRelativePowerMap.map_total Q.ring σ Q.ideal Q.dividedPowers m
    (targetLift a Q) (sourceLift a m Q) (power_difference_mem a m Q) i

theorem naturality {Q P : C} (f : Q ⟶ P) :
    (FrameMaps.BigCrystallineFrameMaps.ambientMap a f).toRingHom.comp (map a m P).toRingHom =
      (map a m Q).toRingHom.comp (FrameMaps.BigCrystallineFrameMaps.ambientMap (fun i => a i ^ m) f).toRingHom :=
  FreeRelative.PowerNaturality.FreeRelativePowerNaturality.square P.ring Q.ring σ
    P.ideal P.dividedPowers Q.ideal Q.dividedPowers m
    (targetLift a P) (sourceLift a m P) (targetLift a Q) (sourceLift a m Q)
    (power_difference_mem a m P) (power_difference_mem a m Q) f.ringMap.toRingHom
    (FrameMaps.BigCrystallineFrameMaps.ambientMap a f).toRingHom
    (FrameMaps.BigCrystallineFrameMaps.ambientMap (fun i => a i ^ m) f).toRingHom
    (FrameMaps.BigCrystallineFrameMaps.ambientMap_relativePD a f)
    (FrameMaps.BigCrystallineFrameMaps.ambientMap_relativePD (fun i => a i ^ m) f)
    (FrameMaps.BigCrystallineFrameMaps.ambientMap_coefficient a f)
    (FrameMaps.BigCrystallineFrameMaps.ambientMap_coefficient (fun i => a i ^ m) f)
    (FrameMaps.BigCrystallineFrameMaps.coordinate_naturality a f)
    (FrameMaps.BigCrystallineFrameMaps.coordinate_naturality (fun i => a i ^ m) f)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.PowerCoordinates.BigCrystallinePowerCoordinates
