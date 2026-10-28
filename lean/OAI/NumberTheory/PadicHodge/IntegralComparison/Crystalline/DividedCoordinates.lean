import OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite
import OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.Nilpotence
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Augmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Poincare

/-! # Divided Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates

noncomputable section

/-!
# IntegralComparison: adjoining divided coordinates in the original crystalline site

Every original big crystalline object admits its actual free divided
coordinate extension. The extension has the same closed subscheme, its
projection has a zero section, and its relative divided de Rham complex
contracts onto the original ambient ring.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

universe u

variable {p : ℕ} {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} (U : BigCrystallineSite.Object p B J δ f) (σ : Type u)

local notation "G" => DividedPowerAlgebra U.ring (σ →₀ U.ring)
local notation "I" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal U.ring σ U.ideal
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers U.ring σ U.ideal U.dividedPowers
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Reduction.MultivariableReduction.augmentation U.ring σ

def residueAugmentation : G ⧸ I →+* U.ring ⧸ U.ideal :=
  Ideal.quotientMap U.ideal (ε).toRingHom
    (Ideal.map_le_iff_le_comap.mp
      (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Augmentation.FreeRelativeAugmentation.isDPMorphism U.ring σ U.ideal U.dividedPowers).ideal_comp)

def residueInclusion : U.ring ⧸ U.ideal →+* G ⧸ I :=
  Ideal.quotientMap I (algebraMap U.ring G)
    (Ideal.map_le_iff_le_comap.mp
      (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.base_isDPMorphism U.ring σ U.ideal U.dividedPowers).ideal_comp)

theorem residue_inclusion_augmentation :
    (residueAugmentation U σ).comp (residueInclusion U σ) = RingHom.id _ := by
  ext x
  change Ideal.Quotient.mk U.ideal (ε (algebraMap U.ring G x)) = Ideal.Quotient.mk U.ideal x
  rw [AlgHom.commutes, Algebra.algebraMap_self_apply]

theorem residue_augmentation_inclusion :
    (residueInclusion U σ).comp (residueAugmentation U σ) = RingHom.id _ := by
  apply RingHom.ext
  intro a
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Ideal.Quotient.mk I (algebraMap U.ring G (ε x)) = Ideal.Quotient.mk I x
  apply Ideal.Quotient.eq.mpr
  rw [AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Augmentation.FreeRelativeAugmentation.ideal_eq_comap]
  change ε (algebraMap U.ring G (ε x) - x) ∈ U.ideal
  simp only [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self, Ideal.zero_mem]

theorem prime_nilpotent : IsNilpotent (p : G) := by
  simpa only [map_natCast] using U.primeNilpotent.map (algebraMap U.ring G)

def augmentationPD : DividedPowers.DPMorphism γ U.dividedPowers where
  toRingHom := (ε).toRingHom
  ideal_comp := (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Augmentation.FreeRelativeAugmentation.isDPMorphism U.ring σ U.ideal U.dividedPowers).ideal_comp
  dpow_comp := (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Augmentation.FreeRelativeAugmentation.isDPMorphism U.ring σ U.ideal U.dividedPowers).dpow_comp

theorem residue_spec_retraction :
    (Spec.map (CommRingCat.ofHom (residueAugmentation U σ)) :
      Spec (CommRingCat.of (U.ring ⧸ U.ideal)) ⟶ Spec (CommRingCat.of (G ⧸ I))) ≫
      Spec.map (CommRingCat.ofHom (residueInclusion U σ)) = 𝟙 _ := by
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((residueAugmentation U σ).comp
    (residueInclusion U σ))) = 𝟙 _
  rw [residue_inclusion_augmentation]
  exact Spec.map_id _

variable [Fact p.Prime]

/-- This is an object of the original IntegralComparison site with the original geometric map. -/
def object : BigCrystallineSite.Object p B J δ f where
  ring := CommRingCat.of G
  base := (algebraMap U.ring G).comp U.base
  ideal := I
  dividedPowers := γ
  baseCompatible := (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.base_isDPMorphism U.ring σ U.ideal U.dividedPowers).comp
    _ U.baseCompatible
  primeNilpotent := prime_nilpotent U σ
  nilIdeal := fun _ hx => DividedPower.Nilpotence.nilpotent_of_mem γ p
    (Fact.out : p.Prime).pos (prime_nilpotent U σ) hx
  mapToX := Spec.map (CommRingCat.ofHom (residueInclusion U σ)) ≫ U.mapToX
  overBase := by
    rw [Category.assoc, U.overBase, ← Category.assoc, ← Spec.map_comp]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1

def projection : object U σ ⟶ U where
  ringMap :=
    { toRingHom := algebraMap U.ring G
      ideal_comp := (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.base_isDPMorphism U.ring σ U.ideal U.dividedPowers).ideal_comp
      dpow_comp := (AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.base_isDPMorphism U.ring σ U.ideal U.dividedPowers).dpow_comp }
  overBase := rfl
  overX := rfl

theorem augmentation_quotientMap :
    BigCrystallineSite.Object.quotientMap U (object U σ) (augmentationPD U σ) = residueAugmentation U σ := rfl

theorem object_mapToX : (object U σ).mapToX =
    Spec.map (CommRingCat.ofHom (residueInclusion U σ)) ≫ U.mapToX := rfl

theorem augmentation_overBase : (augmentationPD U σ).toRingHom.comp (object U σ).base = U.base := by
  ext b
  exact AlgHom.commutes ε (U.base b)

theorem augmentation_overX :
    Spec.map (CommRingCat.ofHom (BigCrystallineSite.Object.quotientMap U (object U σ) (augmentationPD U σ))) ≫
      (object U σ).mapToX = U.mapToX := by
  rw [augmentation_quotientMap, object_mapToX, ← Category.assoc]
  erw [residue_spec_retraction U σ]
  exact Category.id_comp _

def zeroSection : U ⟶ object U σ where
  ringMap := augmentationPD U σ
  overBase := augmentation_overBase U σ
  overX := augmentation_overX U σ

theorem zeroSection_projection : zeroSection U σ ≫ projection U σ = 𝟙 U := by
  apply BigCrystallineSite.Object.Hom.ext
  ext x
  exact AlgHom.commutes ε x

instance relativeAlgebra : Algebra U.ring (object U σ).ring :=
  inferInstanceAs (Algebra U.ring G)

/-- Relative PD Poincaré for the actual divided-coordinate extension. -/
def homotopyEquiv [Fintype σ] : HomotopyEquiv
    ((CochainComplex.single₀ (ModuleCat U.ring)).obj (ModuleCat.of U.ring U.ring))
    (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.complex U.ring (object U σ).ring (object U σ).ideal (object U σ).dividedPowers) :=
  AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Poincare.FreeRelativePoincare.homotopyEquiv U.ring σ U.ideal U.dividedPowers

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.DividedCoordinates
