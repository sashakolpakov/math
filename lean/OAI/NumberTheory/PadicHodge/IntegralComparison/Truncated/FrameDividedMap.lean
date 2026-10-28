import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameAlgebras
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedLiftIdeal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates

/-! # Frame Divided Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameDividedMap

noncomputable section

/-! Native divided coordinates map to an actual smooth truncated-Witt
frame through any étale coordinate chart. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

attribute [local instance] IntegralComparison.Etale.DividedCoordinateLift.scalarAlgebra
  IntegralComparison.Etale.DividedCoordinateLift.scalarTower

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (A C : Type) [CommRing A] [CommRing C]
  [Algebra (Witt.Ring p k n) A]
  [Algebra.Smooth (Witt.Ring p k n) A] [Algebra k C]
  (ρ : A →+* C) (hρ : Function.Surjective ρ)
  (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k,
    ρ (algebraMap (Witt.Ring p k n) A (Witt.quotient p k n w)) =
      algebraMap k C (WittVector.constantCoeff w))
  (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))
  (β : U ⟶ SmoothFrame.object p A C ρ hρ hker k n hbase)
  (σ : Type)

local notation "W" => WittVector p k
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt.Ring p k n
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.object p A C ρ hρ hker k n hbase
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates.object U σ

include β in
omit [Fintype k] in
theorem extension_property : (p : (G).ring) ^ (n + 1) = 0 := by
  simpa only [map_pow, map_natCast, map_zero] using congrArg (algebraMap U.ring (G).ring)
    (FrameAlgebras.frame_property p k n A C ρ hρ hker hbase U β)

variable [Algebra (MvPolynomial σ (Witt.Ring p k n)) A]
  [IsScalarTower (Witt.Ring p k n)
    (MvPolynomial σ (Witt.Ring p k n)) A]
  [Algebra.Etale (MvPolynomial σ (Witt.Ring p k n)) A]

def chartLift : letI := FrameAlgebras.ambientAlgebra p k n A C ρ hρ hker hbase U β;
    A →ₐ[S] DividedPowerAlgebra U.ring (σ →₀ U.ring) := by
  letI := FrameAlgebras.ambientAlgebra p k n A C ρ hρ hker hbase U β
  exact IntegralComparison.Etale.DividedCoordinateLift.lift S σ A U.ring U.ideal p U.dividedPowers
    U.primeNilpotent (FrameAlgebras.chartMap p k n A C ρ hρ hker hbase U β)

def chartLiftRingHom : A →+* DividedPowerAlgebra U.ring (σ →₀ U.ring) := by
  letI := FrameAlgebras.ambientAlgebra p k n A C ρ hρ hker hbase U β
  exact (chartLift p k n A C ρ hρ hker hbase U β σ).toRingHom

omit [Fintype k] in
theorem chartLift_overBase :
    (chartLiftRingHom p k n A C ρ hρ hker hbase U β σ).comp (F).base = (G).base := by
  let := FrameAlgebras.ambientAlgebra p k n A C ρ hρ hker hbase U β
  apply RingHom.ext
  intro w
  exact (chartLift p k n A C ρ hρ hker hbase U β σ).commutes
    (Witt.quotient p k n w)

def relativeMap : DividedPowers.DPMorphism (F).dividedPowers (G).dividedPowers := by
  apply DividedPowers.DPMorphism.mk'
  apply DividedPowers.IsDPMorphism.of_comp
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (F).dividedPowers (G).dividedPowers (F).base
    (chartLiftRingHom p k n A C ρ hρ hker hbase U β σ)
    (by rw [Ideal.map_span, Set.image_singleton, map_natCast]; rfl) (F).baseCompatible
  exact (congrArg (fun φ : W →+* (G).ring =>
    DividedPowers.IsDPMorphism (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (G).dividedPowers φ) (chartLift_overBase p k n A C ρ hρ hker hbase U β σ)).mpr
        (G).baseCompatible

omit [Fintype k] in
theorem augmentation_relativeMap : (Crystalline.DividedCoordinates.augmentationPD U σ).comp
    (relativeMap p k n A C ρ hρ hker hbase U β σ) = β.ringMap := by
  let := FrameAlgebras.ambientAlgebra p k n A C ρ hρ hker hbase U β
  have he := IntegralComparison.Etale.DividedLiftIdeal.augmentation_comp S σ A U.ring U.ideal p U.dividedPowers
    U.primeNilpotent (FrameAlgebras.chartMap p k n A C ρ hρ hker hbase U β)
  apply DFunLike.ext
  intro a
  exact AlgHom.congr_fun he a

omit [Fintype k] in
theorem relativeMap_overBase :
    (relativeMap p k n A C ρ hρ hker hbase U β σ).toRingHom.comp (F).base = (G).base :=
  chartLift_overBase p k n A C ρ hρ hker hbase U β σ

omit [Fintype k] in
theorem quotient_augmentation_relativeMap : (Crystalline.DividedCoordinates.residueAugmentation U σ).comp
    (BigCrystallineSite.Object.quotientMap G F (relativeMap p k n A C ρ hρ hker hbase U β σ)) =
      BigCrystallineSite.Object.quotientMap U F β.ringMap := by
  have h := congrArg (fun φ => BigCrystallineSite.Object.quotientMap U F φ)
    (augmentation_relativeMap p k n A C ρ hρ hker hbase U β σ)
  exact (BigCrystallineSite.Object.quotientMap_comp U G F (Crystalline.DividedCoordinates.augmentationPD U σ)
    (relativeMap p k n A C ρ hρ hker hbase U β σ)).symm.trans h

omit [Fintype k] in
theorem quotient_relativeMap : BigCrystallineSite.Object.quotientMap G F (relativeMap p k n A C ρ hρ hker hbase U β σ) =
    (Crystalline.DividedCoordinates.residueInclusion U σ).comp (BigCrystallineSite.Object.quotientMap U F β.ringMap) := by
  have h := congrArg (fun φ => (Crystalline.DividedCoordinates.residueInclusion U σ).comp φ)
    (quotient_augmentation_relativeMap p k n A C ρ hρ hker hbase U β σ)
  erw [← RingHom.comp_assoc, Crystalline.DividedCoordinates.residue_augmentation_inclusion,
    RingHom.id_comp] at h
  exact h

omit [Fintype k] in
theorem relativeMap_overX : Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap G F
    (relativeMap p k n A C ρ hρ hker hbase U β σ))) ≫ (F).mapToX = (G).mapToX := by
  have hs : Spec.map (CommRingCat.ofHom
      (BigCrystallineSite.Object.quotientMap G F (relativeMap p k n A C ρ hρ hker hbase U β σ))) =
      Spec.map (CommRingCat.ofHom (Crystalline.DividedCoordinates.residueInclusion U σ)) ≫
        Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U F β.ringMap)) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact quotient_relativeMap p k n A C ρ hρ hker hbase U β σ
  rw [hs, Category.assoc, β.overX]
  exact (Crystalline.DividedCoordinates.object_mapToX U σ).symm

def frameMap : G ⟶ F where
  ringMap := relativeMap p k n A C ρ hρ hker hbase U β σ
  overBase := relativeMap_overBase p k n A C ρ hρ hker hbase U β σ
  overX := relativeMap_overX p k n A C ρ hρ hker hbase U β σ

omit [Fintype k] in
theorem zeroSection_frameMap : Crystalline.DividedCoordinates.zeroSection U σ ≫
    frameMap p k n A C ρ hρ hker hbase U β σ = β := by
  apply BigCrystallineSite.Object.Hom.ext
  exact augmentation_relativeMap p k n A C ρ hρ hker hbase U β σ

def cone : BinaryFan U F := BinaryFan.mk (Crystalline.DividedCoordinates.projection U σ)
  (frameMap p k n A C ρ hρ hker hbase U β σ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.FrameDividedMap
