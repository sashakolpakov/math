import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.OneFirst
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.OneSecond
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension

/-! # Symmetry -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Symmetry

noncomputable section

/-! Symmetry of the native categorical Tor modules. Degree one is the
same tensor kernel in both arguments; the proved dimension-shift
isomorphisms give every higher degree. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace Tor

universe u

variable (R : Type u) [CommRing R]

def tensorKernelComm (N : ModuleCat.{u} R) {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    ((tensorRight N).map f).hom.ker ≃ₗ[R] ((tensorLeft N).map f).hom.ker := by
  let e := TensorProduct.comm R M N
  let e' := TensorProduct.comm R M' N
  have hc (x : M ⊗[R] N) : ((tensorLeft N).map f).hom (e x) =
      e' (((tensorRight N).map f).hom x) :=
    TensorProduct.map_comm (LinearMap.id : N →ₗ[R] N) f.hom x
  apply e.ofSubmodules
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ((tensorLeft N).map f).hom (e y) = 0
    rw [hc]
    exact (congrArg e' (LinearMap.mem_ker.mp hy)).trans e'.map_zero
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply e'.injective
    rw [map_zero, ← hc, e.apply_symm_apply]
    exact hx

def oneIso (M N : ModuleCat.{u} R) :
    (((Tor (ModuleCat R) 1).obj M).obj N) ≅ (((Tor (ModuleCat R) 1).obj N).obj M) := by
  let S := M.projectiveShortComplex
  have hS := M.shortExact_projectiveShortComplex
  exact OneFirst.Tor.kernelIso R N S hS ≪≫ (tensorKernelComm R N S.f).toModuleIso ≪≫
    (OneSecond.Tor.kernelIso R N S hS).symm

def positiveIso : (n : ℕ) → (M N : ModuleCat.{u} R) →
    (((Tor (ModuleCat R) (n + 1)).obj M).obj N) ≅ (((Tor (ModuleCat R) (n + 1)).obj N).obj M)
  | 0, M, N => oneIso R M N
  | n + 1, M, N =>
    let S := M.projectiveShortComplex
    let hS := M.shortExact_projectiveShortComplex
    FirstShift.Tor.shiftIso R N S hS n ≪≫ positiveIso n S.X₁ N ≪≫
      (SecondShift.Tor.shiftIso R N S hS n).symm

def iso (M N : ModuleCat.{u} R) (n : ℕ) :
    (((Tor (ModuleCat R) n).obj M).obj N) ≅ (((Tor (ModuleCat R) n).obj N).obj M) :=
  match n with
  | 0 => Flat.Tor.torZeroIso R M N ≪≫ (TensorProduct.comm R M N).toModuleIso ≪≫
      (Flat.Tor.torZeroIso R N M).symm
  | n + 1 => Symmetry.Tor.positiveIso R n M N

theorem length_comm (M N : ModuleCat.{u} R) (n : ℕ) :
    Module.length R (((Tor (ModuleCat R) n).obj M).obj N) =
      Module.length R (((Tor (ModuleCat R) n).obj N).obj M) :=
  (iso R M N n).toLinearEquiv.length_eq

end Tor

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Symmetry
