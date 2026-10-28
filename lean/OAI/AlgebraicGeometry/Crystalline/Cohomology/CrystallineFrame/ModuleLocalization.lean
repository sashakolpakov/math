import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.PrincipalCovers
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.Resolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AffineModuleLocalization

/-! # Module Localization -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.ModuleLocalization.CrystallineFrameModuleLocalization

noncomputable section

/-!
# Native frame forms localize on actual principal opens

The coefficient-linear map of frame ambient rings is a localization over
the original ambient coefficient ring. Every frame-coordinate form term
therefore localizes as a module. After forgetting to Witt scalars, these
maps are the actual transition maps of the native frame resolution.
-/

open _root_.CategoryTheory Opposite
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k B σ : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B] (a : σ → B)
  (Q : Site.Object p k (AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B)) (s : Q.thickening.ring)

local notation "W" => WittVector p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "R" => Q.thickening.ring
local notation "S" => Localization.Away s
local notation "GR" => DividedPowerAlgebra R (σ →₀ R)
local notation "GS" => DividedPowerAlgebra S (σ →₀ S)
local notation "q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallinePrincipal.Opens.CrystallinePrincipalOpens.projection p k X Q s
local notation "J" => RingHom.ker (OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizationReductionKernel.LocalizationReduction.map R Q.residueRing Q.thickening.reduction s)
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizedPD.LocalizedPDThickening.dividedPowers p k Q.residueRing Q.thickening s

def coefficientAlgHom : GR →ₐ[R] GS :=
  Divided.AffineMaps.DividedAffineMaps.map R S σ J δ
    (Lifts.CrystallineFrameLifts.translation a q) (Lifts.CrystallineFrameLifts.translation_mem a q)

def coefficientMap : GR →ₗ[R] GS := (coefficientAlgHom p k B σ a Q s).toLinearMap

theorem coefficientMap_apply (t : GR) :
    coefficientMap p k B σ a Q s t = Map.CrystallineFrameMap.ambientMap a q t := by
  have he : (coefficientAlgHom p k B σ a Q s).toRingHom = (Map.CrystallineFrameMap.ambientMap a q).toRingHom := by
    apply Divided.AffineMaps.DividedAffineMaps.ringHom_ext_of_coordinate R σ
      (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers GS
      (Multivariable.DividedPowers.MultivariableDividedPowers.ideal S σ J) (FreeRelative.Powers.FreeRelativePowers.dividedPowers S σ J δ)
      _ _ (Divided.AffineMaps.DividedAffineMaps.map_isDPMorphism R S σ J δ
        (Lifts.CrystallineFrameLifts.translation a q) (Lifts.CrystallineFrameLifts.translation_mem a q)
        (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers
        (LocalizedPD.LocalizedPDThickening.coefficients_isDPMorphism p k Q.residueRing Q.thickening s))
      (Map.CrystallineFrameMap.ambientMap_relativePD a q)
    · intro r
      have hr : Map.CrystallineFrameMap.ambientMap a q (algebraMap R GR r) =
          algebraMap S GS (algebraMap R S r) := Map.CrystallineFrameMap.ambientMap_coefficient a q r
      exact ((coefficientAlgHom p k B σ a Q s).commutes r).trans
        ((IsScalarTower.algebraMap_apply R S GS r).trans hr.symm)
    · intro i
      exact (Divided.AffineMaps.DividedAffineMaps.map_coordinate R S σ J δ
        (Lifts.CrystallineFrameLifts.translation a q) (Lifts.CrystallineFrameLifts.translation_mem a q) i).trans
          (Map.CrystallineFrameMap.ambientMap_coordinate a q i).symm
  exact RingHom.congr_fun he t

instance coefficientMap_isLocalizedModule : IsLocalizedModule (Submonoid.powers s) (coefficientMap p k B σ a Q s) :=
  Divided.AffineModuleLocalization.DividedAffineModuleLocalization.isLocalizedModule R S σ J δ
    (Lifts.CrystallineFrameLifts.translation a q) (Lifts.CrystallineFrameLifts.translation_mem a q)
    (RingHom.ker Q.thickening.reduction) Q.thickening.dividedPowers
    (LocalizedPD.LocalizedPDThickening.coefficients_isDPMorphism p k Q.residueRing Q.thickening s) (Submonoid.powers s)

def termMap (n : ℕ) : Koszul.Tensor.KoszulTensor.Term W σ GR n →ₗ[R] Koszul.Tensor.KoszulTensor.Term W σ GS n :=
  TensorProduct.AlgebraTensorModule.rTensor W (⋀[W]^n (σ →₀ W)) (coefficientMap p k B σ a Q s)

instance termMap_isLocalizedModule (n : ℕ) : IsLocalizedModule (Submonoid.powers s) (termMap p k B σ a Q s n) := by
  unfold termMap
  infer_instance

theorem termMap_native [Fintype σ] (n : ℕ) :
    (((Koszul.Functor.KoszulFunctor.functor W σ (Operators.CrystallineFrameOperators.functions p k B σ a)
      (Operators.CrystallineFrameOperators.derivative p k B σ a) (Resolution.CrystallineFrameResolution.commute p k B σ a)).map (q).op).f n).hom =
        (termMap p k B σ a Q s n).restrictScalars W := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro t
  apply LinearMap.ext
  intro ω
  change Map.CrystallineFrameMap.ambientMap a q t ⊗ₜ[W] ω = coefficientMap p k B σ a Q s t ⊗ₜ[W] ω
  exact congrArg (fun z : GS => z ⊗ₜ[W] ω) (coefficientMap_apply p k B σ a Q s t).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.ModuleLocalization.CrystallineFrameModuleLocalization
