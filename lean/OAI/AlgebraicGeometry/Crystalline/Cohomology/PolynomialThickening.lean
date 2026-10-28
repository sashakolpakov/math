import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Augmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Poincare
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Thickening

/-! # Polynomial Thickening -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialThickening.CrystallinePolynomialThickening

noncomputable section

/-!
# Relative polynomial PD thickenings over actual crystalline objects

Adjoining free divided coordinates to any affine crystalline thickening
produces another actual crystalline thickening with the same residue
algebra. The coefficient inclusion and augmentation are genuine PD
thickening morphisms. In finitely many coordinates its actual relative
PD de Rham complex contracts onto the original ambient ring.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k A σ : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra k A] (T : PD.Thickening.AffinePDThickening p k A)

local notation "W" => WittVector p k
local notation "R" => T.ring
local notation "I" => RingHom.ker T.reduction
local notation "G" => DividedPowerAlgebra R (σ →₀ R)
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal R σ I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.FreeRelative.Powers.FreeRelativePowers.dividedPowers R σ I T.dividedPowers
local notation "ε" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Reduction.MultivariableReduction.augmentation R σ

def reduction : G →+* A := T.reduction.comp (ε).toRingHom

theorem reduction_surjective : Function.Surjective (CrystallinePolynomialThickening.reduction p k A σ T) := by
  intro a
  obtain ⟨t, ht⟩ := T.reduction_surjective a
  refine ⟨algebraMap R G t, ?_⟩
  change T.reduction (ε (algebraMap R G t)) = a
  rw [AlgHom.commutes, Algebra.algebraMap_self_apply]
  exact ht

theorem reduction_kernel : RingHom.ker (CrystallinePolynomialThickening.reduction p k A σ T) = J :=
  (FreeRelative.Augmentation.FreeRelativeAugmentation.ideal_eq_comap R σ I).symm

def dividedPowers : DividedPowers (RingHom.ker (CrystallinePolynomialThickening.reduction p k A σ T)) :=
  DividedPowers.ofRingEquiv (e := RingEquiv.refl G)
    (by
      change (J).map (RingHom.id G) = _
      rw [Ideal.map_id, reduction_kernel]) γ

theorem identity_isDPMorphism :
    DividedPowers.IsDPMorphism γ (CrystallinePolynomialThickening.dividedPowers p k A σ T) (RingHom.id G) where
  ideal_comp := by rw [Ideal.map_id, reduction_kernel]
  dpow_comp _ _ := rfl

theorem identity_inverse_isDPMorphism :
    DividedPowers.IsDPMorphism (CrystallinePolynomialThickening.dividedPowers p k A σ T) γ (RingHom.id G) where
  ideal_comp := by rw [Ideal.map_id, reduction_kernel]
  dpow_comp _ _ := rfl

theorem coefficients_isDPMorphism :
    DividedPowers.IsDPMorphism T.dividedPowers (CrystallinePolynomialThickening.dividedPowers p k A σ T) (algebraMap R G) :=
  (identity_isDPMorphism p k A σ T).comp _
    (FreeRelative.Powers.FreeRelativePowers.base_isDPMorphism R σ I T.dividedPowers)

theorem augmentation_isDPMorphism :
    DividedPowers.IsDPMorphism (CrystallinePolynomialThickening.dividedPowers p k A σ T) T.dividedPowers (ε).toRingHom :=
  (FreeRelative.Augmentation.FreeRelativeAugmentation.isDPMorphism R σ I T.dividedPowers).comp _
    (identity_inverse_isDPMorphism p k A σ T)

/-- The actual crystalline thickening obtained by adjoining divided coordinates. -/
def thickening : PD.Thickening.AffinePDThickening p k A where
  ring := CommRingCat.of G
  reduction := CrystallinePolynomialThickening.reduction p k A σ T
  reduction_surjective := CrystallinePolynomialThickening.reduction_surjective p k A σ T
  reduction_base := by
    ext w
    change T.reduction (ε (algebraMap W G w)) = _
    rw [IsScalarTower.algebraMap_apply W R G, AlgHom.commutes, Algebra.algebraMap_self_apply]
    exact DFunLike.congr_fun T.reduction_base w
  p_nilpotent := by
    have hp := T.p_nilpotent.map (algebraMap R G)
    simpa only [map_natCast] using hp
  dividedPowers := CrystallinePolynomialThickening.dividedPowers p k A σ T
  baseDP := by
    have hd := (coefficients_isDPMorphism p k A σ T).comp _ T.baseDP
    rw [← IsScalarTower.algebraMap_eq W R G] at hd
    exact hd

instance thickeningRelativeAlgebra : Algebra R (thickening p k A σ T).ring :=
  inferInstanceAs (Algebra R G)

def inclusion : T ⟶ thickening p k A σ T where
  hom := IsScalarTower.toAlgHom W R G
  reduction_comp := by
    ext t
    change T.reduction (ε (algebraMap R G t)) = T.reduction t
    rw [AlgHom.commutes, Algebra.algebraMap_self_apply]
  dp_comp := coefficients_isDPMorphism p k A σ T

def augmentation : thickening p k A σ T ⟶ T where
  hom := (ε).restrictScalars W
  reduction_comp := rfl
  dp_comp := augmentation_isDPMorphism p k A σ T

theorem inclusion_augmentation : inclusion p k A σ T ≫ augmentation p k A σ T = 𝟙 T := by
  apply PD.Thickening.AffinePDThickening.Hom.ext
  ext t
  change ε (algebraMap R G t) = t
  rw [AlgHom.commutes, Algebra.algebraMap_self_apply]

def formsIso : PD.DeRham.PDDeRham.complex R G J γ ≅
    PD.DeRham.PDDeRham.complex R (thickening p k A σ T).ring
      (RingHom.ker (thickening p k A σ T).reduction) (thickening p k A σ T).dividedPowers :=
  PD.DeRhamEquivalence.PDDeRhamEquivalence.complexIso (A := CommAlgCat.of R G) (B := CommAlgCat.of R G)
    (AlgEquiv.refl) (identity_isDPMorphism p k A σ T) (identity_inverse_isDPMorphism p k A σ T)

/-- Relative PD Poincaré on the actual extension of every affine crystalline object. -/
def homotopyEquiv [Fintype σ] : HomotopyEquiv
    ((CochainComplex.single₀ (ModuleCat R)).obj (ModuleCat.of R R))
    (PD.DeRham.PDDeRham.complex R (thickening p k A σ T).ring
      (RingHom.ker (thickening p k A σ T).reduction) (thickening p k A σ T).dividedPowers) :=
  (FreeRelative.Poincare.FreeRelativePoincare.homotopyEquiv R σ I T.dividedPowers).trans
    (HomotopyEquiv.ofIso (formsIso p k A σ T))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PolynomialThickening.CrystallinePolynomialThickening
