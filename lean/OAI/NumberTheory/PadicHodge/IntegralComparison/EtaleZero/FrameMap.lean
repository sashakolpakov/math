import OAI.NumberTheory.PadicHodge.IntegralComparison.Zero.FrameAlgebras
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DividedLiftIdeal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates

/-! # Frame Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameMap

noncomputable section

/-!
# IntegralComparison: free divided coordinates map to the original étale zero frame
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [CharP k p]
  [CommRing C] [Algebra k C] [Algebra (MvPolynomial σ k) C]
  [IsScalarTower k (MvPolynomial σ k) C] [Algebra.Etale (MvPolynomial σ k) C]
  (U : BigCrystallineSite.Object p (WittVector p k) (Ideal.span {(p : WittVector p k)})
    (AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
    (Witt.Crystalline.wittStructureMap p k (Crystalline.Presentation.affineScheme k C)))
  (β : U ⟶ ZeroLevel.LevelFrame.frame p k C)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame.frame p k C
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates.object U σ

def chartLift : letI := Zero.FrameAlgebras.ambientAlgebra p k C U β
    C →ₐ[k] DividedPowerAlgebra U.ring (σ →₀ U.ring) := by
  letI := Zero.FrameAlgebras.ambientAlgebra p k C U β
  exact IntegralComparison.Etale.DividedCoordinateLift.lift k σ C U.ring U.ideal p U.dividedPowers
    U.primeNilpotent (Zero.FrameAlgebras.chartMap p k C U β)

def relativeMap : DividedPowers.DPMorphism (F).dividedPowers (G).dividedPowers := by
  letI := Zero.FrameAlgebras.ambientAlgebra p k C U β
  exact Zero.IdealPDMap.map (G).dividedPowers (chartLift p k C σ U β).toRingHom

theorem augmentation_relativeMap : (Crystalline.DividedCoordinates.augmentationPD U σ).comp
    (relativeMap p k C σ U β) = β.ringMap := by
  let := Zero.FrameAlgebras.ambientAlgebra p k C U β
  have he := IntegralComparison.Etale.DividedLiftIdeal.augmentation_comp k σ C U.ring U.ideal p U.dividedPowers
    U.primeNilpotent (Zero.FrameAlgebras.chartMap p k C U β)
  apply DFunLike.ext
  intro c
  exact AlgHom.congr_fun he c

theorem relativeMap_overBase : (relativeMap p k C σ U β).toRingHom.comp (F).base = (G).base := by
  let := Zero.FrameAlgebras.ambientAlgebra p k C U β
  apply RingHom.ext
  intro w
  change chartLift p k C σ U β (algebraMap k C (WittVector.constantCoeff w)) =
    algebraMap U.ring (G).ring (U.base w)
  rw [AlgHom.commutes]
  change algebraMap U.ring (G).ring (β.ringMap (algebraMap k C (WittVector.constantCoeff w))) = _
  rw [Zero.FrameAlgebras.coefficient_base]

theorem quotient_augmentation_relativeMap : (Crystalline.DividedCoordinates.residueAugmentation U σ).comp
    (BigCrystallineSite.Object.quotientMap G F (relativeMap p k C σ U β)) = BigCrystallineSite.Object.quotientMap U F β.ringMap := by
  have h := congrArg (fun φ => BigCrystallineSite.Object.quotientMap U F φ) (augmentation_relativeMap p k C σ U β)
  exact (BigCrystallineSite.Object.quotientMap_comp U G F (Crystalline.DividedCoordinates.augmentationPD U σ)
    (relativeMap p k C σ U β)).symm.trans h

theorem quotient_relativeMap : BigCrystallineSite.Object.quotientMap G F (relativeMap p k C σ U β) =
    (Crystalline.DividedCoordinates.residueInclusion U σ).comp (BigCrystallineSite.Object.quotientMap U F β.ringMap) := by
  have h := congrArg (fun φ => (Crystalline.DividedCoordinates.residueInclusion U σ).comp φ)
    (quotient_augmentation_relativeMap p k C σ U β)
  erw [← RingHom.comp_assoc, Crystalline.DividedCoordinates.residue_augmentation_inclusion,
    RingHom.id_comp] at h
  exact h

theorem relativeMap_overX : Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap G F
    (relativeMap p k C σ U β))) ≫ (F).mapToX = (G).mapToX := by
  have hs : Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap G F (relativeMap p k C σ U β))) =
      Spec.map (CommRingCat.ofHom (Crystalline.DividedCoordinates.residueInclusion U σ)) ≫
        Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U F β.ringMap)) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact quotient_relativeMap p k C σ U β
  rw [hs, Category.assoc, β.overX]
  exact (Crystalline.DividedCoordinates.object_mapToX U σ).symm

def frameMap : G ⟶ F where
  ringMap := relativeMap p k C σ U β
  overBase := relativeMap_overBase p k C σ U β
  overX := relativeMap_overX p k C σ U β

theorem zeroSection_frameMap : Crystalline.DividedCoordinates.zeroSection U σ ≫
    frameMap p k C σ U β = β := by
  apply BigCrystallineSite.Object.Hom.ext
  exact augmentation_relativeMap p k C σ U β

def cone : BinaryFan U F := BinaryFan.mk (Crystalline.DividedCoordinates.projection U σ)
  (frameMap p k C σ U β)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.EtaleZero.FrameMap
