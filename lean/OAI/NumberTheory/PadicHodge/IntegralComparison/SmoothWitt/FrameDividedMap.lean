import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameAlgebras
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedLiftIdeal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates

/-! # Frame Divided Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameDividedMap

noncomputable section

/-! The native free divided-coordinate extension maps to the actual smooth Witt frame. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameRing

universe u

variable (p : ℕ) [Fact p.Prime] (k A C : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w)) (n : ℕ)
  (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))
  (β : U ⟶ WittFrame.object p k A C ρ hρ hker hbase n)

local notation "W" => WittVector p k
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame.object p k A C ρ hρ hker hbase n

include β in
theorem frame_property : (p : U.ring) ^ (n + 1) = 0 := by
  have hzero : (p : (F).ring) ^ (n + 1) = 0 := FrameRing.prime_power_zero p A n
  simpa only [map_pow, map_natCast, map_zero] using congrArg β.ringMap.toRingHom hzero

variable (σ : Type u)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates.object U σ

local instance coefficientAlgebra : Algebra W U.ring :=
  FrameLifting.ambientAlgebra p k C U

include β in
theorem extension_property : (p : (G).ring) ^ (n + 1) = 0 := by
  simpa only [map_pow, map_natCast, map_zero] using congrArg (algebraMap U.ring (G).ring)
    (frame_property p k A C ρ hρ hker hbase n U β)

variable [Algebra (MvPolynomial σ (WittVector p k)) A]
  [IsScalarTower (WittVector p k) (MvPolynomial σ (WittVector p k)) A]
  [Algebra.Etale (MvPolynomial σ (WittVector p k)) A]

def chartLift : letI := FrameLifting.ambientAlgebra p k C U
    A →ₐ[W] DividedPowerAlgebra U.ring (σ →₀ U.ring) := by
  letI := FrameLifting.ambientAlgebra p k C U
  exact IntegralComparison.Etale.DividedCoordinateLift.lift W σ A U.ring U.ideal p U.dividedPowers
    U.primeNilpotent (FrameAlgebras.chartMap p k A C ρ hρ hker hbase n U β)

theorem chartLift_overBase :
    (chartLift p k A C ρ hρ hker hbase n U β σ).toRingHom.comp (algebraMap W A) = (G).base := by
  apply RingHom.ext
  intro w
  exact (chartLift p k A C ρ hρ hker hbase n U β σ).commutes w

def relativeMap : DividedPowers.DPMorphism (F).dividedPowers (G).dividedPowers :=
  FrameMap.ringMap p k A C n G (extension_property p k A C ρ hρ hker hbase n U β σ)
    (chartLift p k A C ρ hρ hker hbase n U β σ).toRingHom
    (chartLift_overBase p k A C ρ hρ hker hbase n U β σ)

theorem augmentation_relativeMap : (Crystalline.DividedCoordinates.augmentationPD U σ).comp
    (relativeMap p k A C ρ hρ hker hbase n U β σ) = β.ringMap := by
  let := FrameLifting.ambientAlgebra p k C U
  have he := IntegralComparison.Etale.DividedLiftIdeal.augmentation_comp W σ A U.ring U.ideal p U.dividedPowers
    U.primeNilpotent (FrameAlgebras.chartMap p k A C ρ hρ hker hbase n U β)
  apply DFunLike.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact AlgHom.congr_fun he a

theorem relativeMap_overBase :
    (relativeMap p k A C ρ hρ hker hbase n U β σ).toRingHom.comp (F).base = (G).base :=
  FrameMap.overBase p k A C n G (extension_property p k A C ρ hρ hker hbase n U β σ)
    (chartLift p k A C ρ hρ hker hbase n U β σ).toRingHom
    (chartLift_overBase p k A C ρ hρ hker hbase n U β σ)

theorem quotient_augmentation_relativeMap : (Crystalline.DividedCoordinates.residueAugmentation U σ).comp
    (BigCrystallineSite.Object.quotientMap G F (relativeMap p k A C ρ hρ hker hbase n U β σ)) = BigCrystallineSite.Object.quotientMap U F β.ringMap := by
  have h := congrArg (fun φ => BigCrystallineSite.Object.quotientMap U F φ) (augmentation_relativeMap p k A C ρ hρ hker hbase n U β σ)
  exact (BigCrystallineSite.Object.quotientMap_comp U G F (Crystalline.DividedCoordinates.augmentationPD U σ)
    (relativeMap p k A C ρ hρ hker hbase n U β σ)).symm.trans h

theorem quotient_relativeMap : BigCrystallineSite.Object.quotientMap G F (relativeMap p k A C ρ hρ hker hbase n U β σ) =
    (Crystalline.DividedCoordinates.residueInclusion U σ).comp (BigCrystallineSite.Object.quotientMap U F β.ringMap) := by
  have h := congrArg (fun φ => (Crystalline.DividedCoordinates.residueInclusion U σ).comp φ)
    (quotient_augmentation_relativeMap p k A C ρ hρ hker hbase n U β σ)
  erw [← RingHom.comp_assoc, Crystalline.DividedCoordinates.residue_augmentation_inclusion,
    RingHom.id_comp] at h
  exact h

theorem relativeMap_overX : Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap G F
    (relativeMap p k A C ρ hρ hker hbase n U β σ))) ≫ (F).mapToX = (G).mapToX := by
  have hs : Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap G F (relativeMap p k A C ρ hρ hker hbase n U β σ))) =
      Spec.map (CommRingCat.ofHom (Crystalline.DividedCoordinates.residueInclusion U σ)) ≫
        Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U F β.ringMap)) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact quotient_relativeMap p k A C ρ hρ hker hbase n U β σ
  rw [hs, Category.assoc, β.overX]
  exact (Crystalline.DividedCoordinates.object_mapToX U σ).symm

def frameMap : G ⟶ F where
  ringMap := relativeMap p k A C ρ hρ hker hbase n U β σ
  overBase := relativeMap_overBase p k A C ρ hρ hker hbase n U β σ
  overX := relativeMap_overX p k A C ρ hρ hker hbase n U β σ

theorem zeroSection_frameMap : Crystalline.DividedCoordinates.zeroSection U σ ≫
    frameMap p k A C ρ hρ hker hbase n U β σ = β := by
  apply BigCrystallineSite.Object.Hom.ext
  exact augmentation_relativeMap p k A C ρ hρ hker hbase n U β σ

def cone : BinaryFan U F := BinaryFan.mk (Crystalline.DividedCoordinates.projection U σ)
  (frameMap p k A C ρ hρ hker hbase n U β σ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.FrameDividedMap
