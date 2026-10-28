import OAI.NumberTheory.PadicHodge.IntegralComparison.DualComplexHomology
import OAI.AlgebraicGeometry.Crystalline.Cohomology.IntrinsicScalarExtensionExact
import Mathlib.LinearAlgebra.Dual.BaseChange

/-! # Free Dual Base Change -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FreeDualBaseChange

noncomputable section

/-! Finite free coefficient duals commute with the specified scalar extension,
including the actual differentials of a complex. -/

open _root_.CategoryTheory _root_.HomologicalComplex
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

variable (V : Type u) [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V]

def equiv : S ⊗[R] Module.Dual R V ≃ₗ[S] Module.Dual S (S ⊗[R] V) :=
  (TensorProduct.isBaseChange R V S).toDualBaseChange

theorem equiv_tmul_one (a : S) (f : Module.Dual R V) (v : V) :
    equiv R S V (a ⊗ₜ[R] f) (1 ⊗ₜ[R] v) = a * algebraMap R S (f v) :=
  (TensorProduct.isBaseChange R V S).toDualBaseChange_tmul a f v

theorem equiv_tmul (a b : S) (f : Module.Dual R V) (v : V) :
    equiv R S V (a ⊗ₜ[R] f) (b ⊗ₜ[R] v) = a * b * algebraMap R S (f v) := by
  have h : b ⊗ₜ[R] v = b • (1 ⊗ₜ[R] v) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h, map_smul, equiv_tmul_one]
  simp only [smul_eq_mul]
  ring

variable {V}
variable {W : Type u} [AddCommGroup W] [Module R W]
  [Module.Free R W] [Module.Finite R W]

theorem naturality (f : V →ₗ[R] W) :
    (equiv R S V).toLinearMap.comp (f.dualMap.baseChange S) =
      (f.baseChange S).dualMap.comp (equiv R S W).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a g
  apply TensorProduct.AlgebraTensorModule.ext
  intro b v
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul,
    LinearEquiv.coe_coe, LinearMap.dualMap_apply, equiv_tmul]

variable {ι : Type v} {c : ComplexShape ι}

abbrev tensorFunctor := AlgebraicGeometry.Crystalline.Cohomology.IntrinsicScalarExtension.functor R S

def complexIso (K : HomologicalComplex (ModuleCat.{u} R) c)
    [∀ i, Module.Free R (K.X i)] [∀ i, Module.Finite R (K.X i)] :
    ((tensorFunctor R S).mapHomologicalComplex c.symm).obj
        (DualComplexHomology.complex R K) ≅
      DualComplexHomology.complex S
        (((tensorFunctor R S).mapHomologicalComplex c).obj K) :=
  Hom.isoOfComponents (fun i => (equiv R S (K.X i)).toModuleIso) (by
    intro i j hij
    exact ModuleCat.hom_ext (naturality R S (K.d j i).hom).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FreeDualBaseChange
