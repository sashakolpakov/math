import OAI.RepresentationTheory.Theta.Geometric.CotangentValueExt
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Point Cotangent Pairing -/

namespace OAI.RepresentationTheory.Theta.Geometric.PointCotangentPairing

noncomputable section

/-! The intrinsic point-derivation space is the full dual of the
cotangent fiber. In particular, its pairings detect every cotangent vector. -/

open scoped TensorProduct

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations

variable {A : Type} [CommRing A] [Algebra ℂ A]
    [Algebra A ℂ] [IsScalarTower ℂ A ℂ]
    (p : A →ₐ[ℂ] ℂ) (hp : ∀ a, algebraMap A ℂ a = p a)

def pointDerivationLinearEquiv : AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations.pointDerivations p ≃ₗ[ℂ] Derivation ℂ A ℂ where
  toFun δ := {
    toLinearMap := δ.val
    map_one_eq_zero' := δ.property.1
    leibniz' a b := by simpa only [Algebra.smul_def, hp] using δ.property.2 a b }
  invFun δ := ⟨δ.toLinearMap, δ.map_one_eq_zero,
    fun a b => by
      change δ (a * b) = p a * δ b + p b * δ a
      simpa only [Algebra.smul_def, hp] using δ.leibniz a b⟩
  left_inv δ := rfl
  right_inv δ := rfl
  map_add' δ ε := rfl
  map_smul' c δ := rfl

def pointCotangentPairingEquiv : AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations.pointDerivations p ≃ₗ[ℂ] Module.Dual ℂ (PointCotangent.pointCotangent ℂ A) :=
  (pointDerivationLinearEquiv p hp).trans (PointCotangent.pointDerivationEquiv ℂ A ℂ)

theorem pointCotangentPairingEquiv_D (δ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations.pointDerivations p) (a : A) :
    pointCotangentPairingEquiv p hp δ (1 ⊗ₜ[A] KaehlerDifferential.D ℂ A a) = δ.val a :=
  PointCotangent.pointDerivationEquiv_D ℂ A ℂ _ a

theorem pointCotangentPairing_separates (v : PointCotangent.pointCotangent ℂ A)
    (hv : ∀ δ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointDerivations.pointDerivations p, pointCotangentPairingEquiv p hp δ v = 0) : v = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff ℂ v).mp
  intro f
  obtain ⟨δ, rfl⟩ := (pointCotangentPairingEquiv p hp).surjective f
  exact hv δ

end

end OAI.RepresentationTheory.Theta.Geometric.PointCotangentPairing
