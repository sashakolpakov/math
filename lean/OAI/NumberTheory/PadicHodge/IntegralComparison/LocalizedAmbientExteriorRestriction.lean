import OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedConormalResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KaehlerBaseChange

/-! # Localized Ambient Exterior Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedAmbientExteriorRestriction.ConormalResidue

noncomputable section

/-! The native ambient exterior base-change map respects the two
successive scalar extensions from an ambient ring and its quotient. -/

open _root_.Module _root_.Algebra.Extension KaehlerDifferential
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedQuotientExtension
open OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  (r : A) [IsLocalization.Away r B] (I : Ideal A)

local instance ambientBaseTower : IsScalarTower k (A ⧸ I) (B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) :=
  AlgebraicGeometry.Resolution.Blowups.Smooth.TransformedCoordinateHypersurface.Construction.extendedQuotient_scalarTower I

theorem ambient_one_tmul (ω : Ω[A⁄k]) :
    LocalizedConormalResidue.ambient (k := k) (B := B) r I (1 ⊗ₜ[A ⧸ I] (1 ⊗ₜ[A] ω)) =
      1 ⊗ₜ[B] KaehlerDifferential.map k k A B ω := by
  have hω : ω ∈ Submodule.span A (Set.range (D k A)) := by
    rw [span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem ω hω =>
    obtain ⟨a, rfl⟩ := hω
    rw [LocalizedConormalResidue.ambient_tmul_D, map_one, mul_one, map_D]
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | add x y hx hy ihx ihy => simp only [TensorProduct.tmul_add, map_add, ihx, ihy]
  | smul a ω hω ih =>
    rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul, LinearMapClass.map_smul_of_tower,
      ih, map_smul, TensorProduct.tmul_smul]

def exteriorMap (n : ℕ) :=
  (exteriorPower.map n (LocalizedConormalResidue.ambient (k := k) (B := B) r I).toLinearMap).comp
    (GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap (A ⧸ I) (B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) ((A ⧸ I) ⊗[A] Ω[A⁄k]) n)

theorem exteriorMap_scalar_one (n : ℕ) (ω : ⋀[A]^n Ω[A⁄k]) :
    exteriorMap (k := k) (B := B) r I n
      (1 ⊗ₜ[A ⧸ I] GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap A (A ⧸ I) Ω[A⁄k] n (1 ⊗ₜ[A] ω)) =
    GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap B (B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) Ω[B⁄k] n
      (1 ⊗ₜ[B] AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (Exterior.KaehlerBaseChange.algebraHom (k := k) (A := A) (B := B)) n ω) := by
  have hω : ω ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem ω hω =>
    obtain ⟨v, rfl⟩ := hω
    rw [AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap_mk]
    simp only [exteriorMap, LinearMap.comp_apply, GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap_tmul_ιMulti,
      one_smul, exteriorPower.map_apply_ιMulti]
    apply congrArg (exteriorPower.ιMulti (B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) n)
    funext i
    dsimp only [Function.comp_apply]
    exact (ambient_one_tmul r I (v i)).trans
      (congrArg (fun ω : Ω[B⁄k] => (1 : B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) ⊗ₜ[B] ω)
        (Exterior.KaehlerBaseChange.oneFormsMap_algebraHom (k := k) (B := B) (v i)).symm)
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | add x y hx hy ihx ihy => simp only [TensorProduct.tmul_add, map_add, ihx, ihy]
  | smul a ω hω ih =>
    rw [TensorProduct.tmul_smul, LinearMap.map_smul_of_tower,
      TensorProduct.tmul_smul, LinearMap.map_smul_of_tower, ih,
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap_smul, TensorProduct.tmul_smul, LinearMap.map_smul_of_tower]
    exact algebraMap_smul B a _

theorem exteriorMap_scalar_tmul (n : ℕ) (a : A ⧸ I) (ω : ⋀[A]^n Ω[A⁄k]) :
    exteriorMap (k := k) (B := B) r I n
      (1 ⊗ₜ[A ⧸ I] GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap A (A ⧸ I) Ω[A⁄k] n (a ⊗ₜ[A] ω)) =
    GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap B (B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) Ω[B⁄k] n
      (algebraMap (A ⧸ I) (B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) a ⊗ₜ[B]
        AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (Exterior.KaehlerBaseChange.algebraHom (k := k) (A := A) (B := B)) n ω) := by
  have hsource : GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap A (A ⧸ I) Ω[A⁄k] n (a ⊗ₜ[A] ω) =
      a • GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap A (A ⧸ I) Ω[A⁄k] n (1 ⊗ₜ[A] ω) := by
    rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul]
  have htarget (b : B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) (η : ⋀[B]^n Ω[B⁄k]) :
      GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap B (B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) Ω[B⁄k] n (b ⊗ₜ[B] η) =
        b • GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap B (B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) Ω[B⁄k] n (1 ⊗ₜ[B] η) := by
    rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul]
  rw [hsource, TensorProduct.tmul_smul, LinearMap.map_smul_of_tower,
    exteriorMap_scalar_one,
    htarget (algebraMap (A ⧸ I) (B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) a)]
  exact (algebraMap_smul (B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) a
    (GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap B (B ⧸ LocalizedQuotientExtension.extendedIdeal (B := B) I) Ω[B⁄k] n
      (1 ⊗ₜ[B] AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap
        (Exterior.KaehlerBaseChange.algebraHom (k := k) (A := A) (B := B)) n ω))).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LocalizedAmbientExteriorRestriction.ConormalResidue
