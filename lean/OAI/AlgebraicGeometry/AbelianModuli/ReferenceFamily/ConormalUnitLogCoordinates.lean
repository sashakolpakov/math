import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CoefficientUnitLogarithms
import Mathlib.LinearAlgebra.Dual.Basis

/-! # Conormal Unit Log Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConormalUnitLogCoordinates

noncomputable section

/-! A finite conormal basis expands the actual logarithmic derivative
as a sum of tangent coordinates times constant-direction logarithms.
The identity uses coefficient-linear derivation coordinates. -/

open scoped BigOperators

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]
    (B : Type*) [CommRing B] [Algebra k B]

def coefficientCovector (l : V →ₗ[k] k) : V →ₗ[k] B :=
  (Algebra.linearMap k B).comp l

theorem coefficientCovector_apply (l : V →ₗ[k] k) (v : V) :
    coefficientCovector B l v = algebraMap k B (l v) := rfl

variable {I : Type*} [Fintype I] (b : Module.Basis I k V)

theorem coefficientCovector_basis_sum (f : V →ₗ[k] B) :
    ∑ i, f (b i) • coefficientCovector B (b.coord i) = f := by
  classical
  apply b.ext
  intro j
  simp [coefficientCovector, Module.Basis.coord_apply, Finsupp.single_apply]

def derivationUnitLogCoefficientLinear (u : Bˣ) : Derivation k B B →ₗ[B] B where
  toFun d := CoefficientUnitLogarithms.coefficientUnitLog d u
  map_add' d e := by
    change (d u.val + e u.val) * _ = _
    exact add_mul _ _ _
  map_smul' c d := by
    change (c * d u.val) * (u⁻¹).val = c * (d u.val * (u⁻¹).val)
    exact mul_assoc _ _ _

def conormalUnitLogCoordinate
    (F : Derivation k B B ≃ₗ[B] (V →ₗ[k] B)) (u : Bˣ) (i : I) : B :=
  CoefficientUnitLogarithms.coefficientUnitLog (F.symm (coefficientCovector B (b.coord i))) u

theorem coefficientUnitLog_conormal_expansion
    (F : Derivation k B B ≃ₗ[B] (V →ₗ[k] B)) (u : Bˣ) (d : Derivation k B B) :
    CoefficientUnitLogarithms.coefficientUnitLog d u = ∑ i, F d (b i) * conormalUnitLogCoordinate B b F u i := by
  let L := (derivationUnitLogCoefficientLinear B u).comp F.symm.toLinearMap
  have h := congrArg L (coefficientCovector_basis_sum B b (F d))
  rw [map_sum] at h
  simp only [map_smul] at h
  have hr : L (F d) = CoefficientUnitLogarithms.coefficientUnitLog d u :=
    congrArg (fun e => CoefficientUnitLogarithms.coefficientUnitLog e u) (F.symm_apply_apply d)
  exact hr.symm.trans h.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ConormalUnitLogCoordinates
