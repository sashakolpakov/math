import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.FractionRing

/-! # Rational Scalar Extension -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles

noncomputable section

/-!
# Rational scalar extension and homology

Rationalization is the actual extension-of-scalars functor from integral modules
to rational modules. Its exactness follows from the localization description of
the rational numbers, and gives the native homology comparison for chain
complexes. The unit-module comparison is the tensor-product right unitor, with
its value on elementary tensors recorded explicitly.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

/-- Rationalization of integral modules by the canonical inclusion into `ℚ`. -/
def rationalizeModules : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} ℚ :=
  ModuleCat.extendScalars (Int.castRingHom ℚ)

/-- Flatness comes from the actual fraction-ring localization of `ℤ`. -/
theorem rationalModule_flat : Module.Flat ℤ ℚ :=
  IsLocalization.flat ℚ (nonZeroDivisors ℤ)

/-- The canonical integer-to-rational ring homomorphism is flat. -/
theorem rationalCast_flat : (Int.castRingHom ℚ).Flat := by
  change (algebraMap ℤ ℚ).Flat
  exact RingHom.flat_algebraMap_iff.mpr rationalModule_flat

instance rationalizeModules_isLeftAdjoint : rationalizeModules.IsLeftAdjoint := by
  unfold rationalizeModules
  infer_instance

instance rationalizeModules_preservesColimits : PreservesColimits rationalizeModules := by
  infer_instance

instance rationalizeModules_preservesFiniteLimits :
    PreservesFiniteLimits rationalizeModules :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat rationalCast_flat

instance rationalizeModules_preservesZeroMorphisms :
    rationalizeModules.PreservesZeroMorphisms := by
  infer_instance

instance rationalizeModules_additive : rationalizeModules.Additive :=
  Functor.additive_of_preserves_binary_products rationalizeModules

instance rationalizeModules_preservesHomology : rationalizeModules.PreservesHomology := by
  infer_instance

/-- The degreewise rationalization functor also preserves small colimits. -/
instance rationalizeModules_chain_preservesColimits :
    PreservesColimits (rationalizeModules.mapHomologicalComplex (ComplexShape.down ℕ)) where
  preservesColimitsOfShape := by
    intros
    infer_instance

/-- Exact rationalization commutes with the native homology of chain complexes. -/
def rationalizeHomologyIso (C : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) :
    ((rationalizeModules.mapHomologicalComplex (ComplexShape.down ℕ)).obj C).homology n ≅
      rationalizeModules.obj (C.homology n) :=
  (C.sc n).mapHomologyIso rationalizeModules

/-- The homology comparison respects all actual integral chain maps. -/
@[reassoc]
theorem rationalizeHomologyIso_hom_naturality
    {C D : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : C ⟶ D) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((rationalizeModules.mapHomologicalComplex (ComplexShape.down ℕ)).map f) n ≫
        (rationalizeHomologyIso D n).hom =
      (rationalizeHomologyIso C n).hom ≫
        rationalizeModules.map (HomologicalComplex.homologyMap f n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map f) rationalizeModules

/-- Rationalizing the integral unit module gives the rational unit module. -/
def rationalizeUnitIso :
    rationalizeModules.obj (ModuleCat.of ℤ ℤ) ≅ ModuleCat.of ℚ ℚ :=
  (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).toModuleIso

/-- Elementary tensors are sent to the product of their rational coefficients. -/
@[simp]
theorem rationalizeUnitIso_hom_tmul (q : ℚ) (z : ℤ) :
    rationalizeUnitIso.hom (q ⊗ₜ[ℤ, Int.castRingHom ℚ] z) = q * (z : ℚ) := by
  change z • q = q * (z : ℚ)
  simp [zsmul_eq_mul, mul_comm]

/-- In particular, the scalar extension of an integer has its usual rational value. -/
@[simp]
theorem rationalizeUnitIso_hom_one_tmul (z : ℤ) :
    rationalizeUnitIso.hom ((1 : ℚ) ⊗ₜ[ℤ, Int.castRingHom ℚ] z) = (z : ℚ) := by
  simpa only [one_mul] using rationalizeUnitIso_hom_tmul (1 : ℚ) z

/-- The inverse inserts an elementary tensor with integral unit. -/
@[simp]
theorem rationalizeUnitIso_inv_apply (q : ℚ) :
    rationalizeUnitIso.inv q = q ⊗ₜ[ℤ, Int.castRingHom ℚ] (1 : ℤ) :=
  rfl

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.RationalScalarExtension.Cycles
