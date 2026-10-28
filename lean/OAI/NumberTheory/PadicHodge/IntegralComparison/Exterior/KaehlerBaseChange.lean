import OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ExteriorPowerBaseChange
import Mathlib.RingTheory.Etale.Kaehler

/-! # Kaehler Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KaehlerBaseChange

noncomputable section

/-! Exterior scalar extension followed by the universal Kähler map is
the original algebraic de Rham restriction map. -/

open _root_.CategoryTheory KaehlerDifferential
open scoped TensorProduct

open OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange

universe u
variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

abbrev algebraHom : CommAlgCat.of k A ⟶ CommAlgCat.of k B :=
  CommAlgCat.ofHom (IsScalarTower.toAlgHom k A B)

theorem oneFormsMap_algebraHom (ω : Ω[A⁄k]) :
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.oneFormsMap (algebraHom (k := k) (A := A) (B := B)) ω =
      KaehlerDifferential.map k k A B ω := by
  have hω : ω ∈ Submodule.span A (Set.range (D k A)) := by
    rw [span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem ω hω =>
    obtain ⟨a, rfl⟩ := hω
    rw [AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.oneFormsMap_D, map_D]
    rfl
  | zero => simp only [map_zero]
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy]
  | smul a ω hω ih =>
    rw [AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.oneFormsMap_smul, ih, map_smul]
    exact algebraMap_smul B a (KaehlerDifferential.map k k A B ω)

theorem map_one (n : ℕ) (ω : ⋀[A]^n Ω[A⁄k]) :
    exteriorPower.map n (mapBaseChange k A B)
      (GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap A B Ω[A⁄k] n (1 ⊗ₜ[A] ω)) =
        AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (algebraHom (k := k) (A := A) (B := B)) n ω := by
  have hω : ω ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem ω hω =>
    obtain ⟨v, rfl⟩ := hω
    rw [GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap_tmul_ιMulti, one_smul, exteriorPower.map_apply_ιMulti, AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap_mk]
    congr 1
    funext i
    dsimp only [Function.comp_apply]
    rw [mapBaseChange_tmul, one_smul, oneFormsMap_algebraHom]
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | add x y hx hy ihx ihy => simp only [TensorProduct.tmul_add, map_add, ihx, ihy]
  | smul a ω hω ih =>
    rw [TensorProduct.tmul_smul, LinearMap.map_smul_of_tower,
      LinearMap.map_smul_of_tower, ih, AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap_smul]
    exact algebraMap_smul B a _

theorem etale_map_one [Algebra.FormallyEtale A B] (n : ℕ) (ω : ⋀[A]^n Ω[A⁄k]) :
    exteriorPower.map n (tensorKaehlerEquivOfFormallyEtale k A B).toLinearMap
      (GeometricComparison.Integral.ExteriorPowerBaseChange.IntegralExteriorBaseChange.powerScalarMap A B Ω[A⁄k] n (1 ⊗ₜ[A] ω)) =
        AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap (algebraHom (k := k) (A := A) (B := B)) n ω :=
  map_one n ω

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Exterior.KaehlerBaseChange
