import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.PolynomialPoincare
import OAI.AlgebraicGeometry.Crystalline.Cohomology.SplitCochain
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology

/-! # Homotopy -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Homotopy.WittPolynomialHomotopy

noncomputable section

/-!
# A homotopy equivalence for the completed crystalline local calculation

The actual inverse-limit PD de Rham complex of the rank-one Witt tower
contracts onto W(k) in degree zero. The homotopy is its compatible
integral primitive, transported through the degree-zero identification.
-/

open _root_.CategoryTheory Limits

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Tower.WittPolynomialTower.tower p k
local notation "F" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham.complex p k k T
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit.PDInverseLimit.Ring p k k T
local notation "A" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Poincare.WittPolynomialPoincare.coefficients p k
local notation "F₀" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham.CompletedForm p k k T 0
local notation "F₁" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham.CompletedForm p k k T 1
local notation "e" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham.degreeZeroEquiv p k k T
local notation "c" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Poincare.WittPolynomialPoincare.constants p k
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Poincare.WittPolynomialPoincare.constantCoefficient p k
local notation "s" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Poincare.WittPolynomialPoincare.primitiveForms p k
local notation "d" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham.differentialRing p k k T

def augmentationZero : A →ₗ[W] F₀ := (e).symm.toLinearMap.comp c

def projectionZero : F₀ →ₗ[W] A := (r).comp (e).toLinearMap

def primitive : F₁ →ₗ[W] F₀ := (e).symm.toLinearMap.comp s

def augmentationZeroHom : ModuleCat.of W A ⟶ (F).X 0 := ModuleCat.ofHom (augmentationZero p k)

def projectionZeroHom : (F).X 0 ⟶ ModuleCat.of W A := ModuleCat.ofHom (projectionZero p k)

def primitiveHom : (F).X 1 ⟶ (F).X 0 := ModuleCat.ofHom (primitive p k)

theorem differential_augmentation :
    augmentationZeroHom p k ≫ (F).d 0 1 = 0 := by
  change ModuleCat.ofHom (augmentationZero p k) ≫
    ModuleCat.ofHom (PD.PDDeRham.differential p k k T 0) = 0
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact Poincare.WittPolynomialPoincare.differential_constants p k a

theorem projection_augmentation :
    augmentationZeroHom p k ≫ projectionZeroHom p k =
      𝟙 (ModuleCat.of W A) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change r (e ((e).symm (c a))) = a
  rw [LinearEquiv.apply_symm_apply]
  exact Poincare.WittPolynomialPoincare.constantCoefficient_constants p k a

theorem primitive_differential :
    (F).d 0 1 ≫ primitiveHom p k +
      projectionZeroHom p k ≫ augmentationZeroHom p k =
        𝟙 ((F).X 0) := by
  change ModuleCat.ofHom (PD.PDDeRham.differential p k k T 0) ≫
    ModuleCat.ofHom (primitive p k) + ModuleCat.ofHom (projectionZero p k) ≫
      ModuleCat.ofHom (augmentationZero p k) = 𝟙 (ModuleCat.of W F₀)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change F₀ at a
  apply (e).injective
  change e ((e).symm (s (PD.PDDeRham.differential p k k T 0 a)) +
    (e).symm (c (r (e a)))) = e a
  rw [map_add, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hd : PD.PDDeRham.differential p k k T 0 a = d (e a) := by
    change _ = PD.PDDeRham.differential p k k T 0 ((e).symm (e a))
    rw [LinearEquiv.symm_apply_apply]
  rw [hd]
  exact Poincare.WittPolynomialPoincare.primitive_differential p k (e a)

theorem differential_primitive :
    primitiveHom p k ≫ (F).d 0 1 = 𝟙 ((F).X 1) := by
  change ModuleCat.ofHom (primitive p k) ≫
    ModuleCat.ofHom (PD.PDDeRham.differential p k k T 0) = 𝟙 (ModuleCat.of W F₁)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  exact Poincare.WittPolynomialPoincare.differential_primitive p k ω

theorem higher_isZero (n : ℕ) (hn : 2 ≤ n) : IsZero ((F).X n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y => ?_⟩
  exact (Poincare.WittPolynomialPoincare.higher_form_eq_zero p k n hn x).trans
    (Poincare.WittPolynomialPoincare.higher_form_eq_zero p k n hn y).symm

def coefficientsHomotopyEquiv : HomotopyEquiv ((CochainComplex.single₀ (ModuleCat.{u} W)).obj
    (ModuleCat.of W A)) F :=
  SplitCochain.SplitCochainContraction.homotopyEquiv F (ModuleCat.of W A)
    (augmentationZeroHom p k) (projectionZeroHom p k)
    (primitiveHom p k) (differential_augmentation p k) (projection_augmentation p k)
    (primitive_differential p k) (differential_primitive p k) (higher_isZero p k)

/-- The actual completed local crystalline complex is homotopy equivalent to W(k)[0]. -/
def homotopyEquiv : HomotopyEquiv ((CochainComplex.single₀ (ModuleCat.{u} W)).obj
    (ModuleCat.of W W)) F :=
  (HomotopyEquiv.ofIso ((CochainComplex.single₀ (ModuleCat.{u} W)).mapIso
    (PolynomialPoincare.WittPolynomialPoincare.coefficientsEquiv p k).toModuleIso)).trans
      (coefficientsHomotopyEquiv p k)

/-- The local augmentation used by the homotopy equivalence. -/
def augmentation : (CochainComplex.single₀ (ModuleCat.{u} W)).obj (ModuleCat.of W W) ⟶ F :=
  (homotopyEquiv p k).hom

/-- The local augmentation induces isomorphisms on all cohomology objects. -/
instance augmentation_quasiIso : QuasiIso (augmentation p k) :=
  HomotopyEquiv.quasiIso_hom (homotopyEquiv p k)

def degreeZeroHomologyIso : (F).homology 0 ≅ ModuleCat.of W W :=
  ((homotopyEquiv p k).toHomologyIso 0).symm ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 (ModuleCat.of W W)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Homotopy.WittPolynomialHomotopy
