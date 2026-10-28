import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic

/-! # Hermitian Matrix Form -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm

noncomputable section

/-! The literal matrix expression used by ReferenceFamily is a bundled Hermitian
form, linear in its first argument and conjugate-linear in its second. -/

def complexHermitianMatrixForm (H : Matrix (Fin 3) (Fin 3) ℂ) :
    (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) →ₗ⋆[ℂ] ℂ :=
  Matrix.toLinearMap₂'Aux (RingHom.id ℂ) (starRingEnd ℂ) H

theorem complexHermitianMatrixForm_apply (H : Matrix (Fin 3) (Fin 3) ℂ) (x y : Fin 3 → ℂ) :
    complexHermitianMatrixForm H x y = ∑ i, ∑ j, x i * H i j * star (y j) := by
  change (∑ i, ∑ j, star (y j) • (x i) • H i j) = _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change star (y j) * (x i * H i j) = _
  ring

theorem complexHermitianMatrixForm_symmetry (H : Matrix (Fin 3) (Fin 3) ℂ)
    (hH : ∀ i j, H i j = star (H j i)) (x y : Fin 3 → ℂ) :
    complexHermitianMatrixForm H y x = star (complexHermitianMatrixForm H x y) := by
  rw [complexHermitianMatrixForm_apply, complexHermitianMatrixForm_apply]
  simp only [star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [hH i j]
  ring

def restrictHermitianForm {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (P : Submodule ℂ V) : P →ₗ[ℂ] P →ₗ⋆[ℂ] ℂ :=
  (F.comp P.subtype).compl₂ P.subtype

theorem restrictHermitianForm_apply {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (P : Submodule ℂ V) (x y : P) :
    restrictHermitianForm F P x y = F x.val y.val := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.HermitianMatrixForm
