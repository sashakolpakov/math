import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ParameterScheme
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Linear Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.LinearCoordinates

noncomputable section

/-!
Changing coordinates in the ambient finite free module preserves the actual
Grassmannian quotient and its rank. This transports the constructed affine
classification to any module supplied with coordinate equivalences.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable {W : Type w} [AddCommGroup W] [Module R W] {r : ℕ}

def grassmannLinearTransport (e : V ≃ₗ[R] W) (N : Module.Grassmannian R V r) :
    Module.Grassmannian R W r where
  toSubmodule := N.toSubmodule.map e.toLinearMap
  finite_quotient := Module.Finite.equiv (Submodule.Quotient.equiv _ _ e rfl)
  projective_quotient := Module.Projective.of_equiv (Submodule.Quotient.equiv _ _ e rfl)
  rankAtStalk_eq p :=
    (congrFun (Module.rankAtStalk_eq_of_equiv (Submodule.Quotient.equiv _ _ e rfl)) p).symm.trans
      (N.rankAtStalk_eq p)

theorem grassmannLinearTransport_inverse (e : V ≃ₗ[R] W) (N : Module.Grassmannian R V r) :
    grassmannLinearTransport e.symm (grassmannLinearTransport e N) = N := by
  apply Module.Grassmannian.ext
  change (N.toSubmodule.map e.toLinearMap).map e.symm.toLinearMap = N.toSubmodule
  rw [← Submodule.map_comp]
  have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    exact e.symm_apply_apply
  rw [he, Submodule.map_id]

def grassmannLinearEquiv (e : V ≃ₗ[R] W) :
    Module.Grassmannian R V r ≃ Module.Grassmannian R W r where
  toFun := grassmannLinearTransport e
  invFun := grassmannLinearTransport e.symm
  left_inv := grassmannLinearTransport_inverse e
  right_inv := grassmannLinearTransport_inverse e.symm

variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
variable {S : Scheme.{u}} (A : CommRingCat.{u}) (f : Spec A ⟶ S)
variable {L : Type u} [AddCommGroup L] [Module A L]

def grassmannCoordinateAffinePointEquiv (e : L ≃ₗ[A] (ν → A)) :
    Module.Grassmannian A L (Fintype.card ι) ≃
      (Over.mk f ⟶ ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S) :=
  (grassmannLinearEquiv e).trans (ParameterScheme.grassmannParameterAffinePointEquiv A f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.LinearCoordinates
