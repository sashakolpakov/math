import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AffineLocalization
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-! # Affine Module Localization -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AffineModuleLocalization.DividedAffineModuleLocalization

noncomputable section

/-!
# Affine divided-coordinate maps localize coefficient modules

The proved ring localization also localizes the actual module over the
original coefficient ring. Tensoring with any module over a smaller base
preserves this localization property, as needed for frame form modules.
-/

universe u

variable (R S σ : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (I : Ideal S) (δ : DividedPowers I) (b : σ → S) (hb : ∀ i, b i ∈ I)
  (IR : Ideal R) (δR : DividedPowers IR)
  (hbase : DividedPowers.IsDPMorphism δR δ (algebraMap R S))

local notation "GR" => DividedPowerAlgebra R (σ →₀ R)
local notation "GS" => DividedPowerAlgebra S (σ →₀ S)
local notation "f" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AffineMaps.DividedAffineMaps.map R S σ I δ b hb

include hbase in
theorem isLocalizedModule (M : Submonoid R) [IsLocalization M S] :
    IsLocalizedModule M (f).toLinearMap := by
  let : Algebra GR GS := (f).toRingHom.toAlgebra
  have : IsScalarTower R GR GS := IsScalarTower.of_algebraMap_eq' (f).comp_algebraMap.symm
  have : IsLocalization (Algebra.algebraMapSubmonoid GR M) GS :=
    ⟨AffineLocalization.DividedAffineLocalization.isLocalizationMap R S σ I δ b hb IR δR hbase M⟩
  change IsLocalizedModule M (IsScalarTower.toAlgHom R GR GS).toLinearMap
  infer_instance

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.AffineModuleLocalization.DividedAffineModuleLocalization
