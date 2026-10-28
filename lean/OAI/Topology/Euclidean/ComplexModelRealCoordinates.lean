import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Complex Model Real Coordinates -/

namespace OAI.Topology.Euclidean.ComplexModelRealCoordinates.Globalization

noncomputable section

/-!
# Explicit real coordinates for finite-dimensional complex model spaces

The real parts of a complex vector precede its imaginary parts. The construction
uses the standard real/imaginary coordinate equivalence for `ℂ` and an explicit
finite-index reindexing, rather than a chosen vector-space basis. Both directions
are real continuous linear maps, hence smooth of every order.
-/

open scoped _root_.Manifold ContDiff

/-- Concatenate the real and imaginary coordinate index sets. -/
def complexRealCoordinateIndexEquiv (d : ℕ) : Fin d ⊕ Fin d ≃ Fin (2 * d) :=
  finSumFinEquiv.trans (finCongr (two_mul d).symm)

/-- Real and imaginary parts, with a separate summand for each coordinate block. -/
def complexModelRealSumLinearEquiv (d : ℕ) :
    (Fin d → ℂ) ≃ₗ[ℝ] (Fin d ⊕ Fin d → ℝ) where
  toFun z := Sum.elim (fun i => (z i).re) (fun i => (z i).im)
  invFun x i := Complex.equivRealProdCLM.symm (x (Sum.inl i), x (Sum.inr i))
  left_inv z := by
    funext i
    exact Complex.equivRealProdCLM.symm_apply_apply (z i)
  right_inv x := by
    funext i
    cases i <;> rfl
  map_add' z w := by
    funext i
    cases i with
    | inl j => exact Complex.reLm.map_add (z j) (w j)
    | inr j => exact Complex.imLm.map_add (z j) (w j)
  map_smul' c z := by
    funext i
    cases i with
    | inl j => exact Complex.reLm.map_smul c (z j)
    | inr j => exact Complex.imLm.map_smul c (z j)

/-- The explicit real-linear coordinate equivalence `ℂᵈ ≃ ℝ²ᵈ`. -/
def complexModelRealLinearEquiv (d : ℕ) :
    (Fin d → ℂ) ≃ₗ[ℝ] (Fin (2 * d) → ℝ) :=
  (complexModelRealSumLinearEquiv d).trans
    (LinearEquiv.funCongrLeft ℝ ℝ (complexRealCoordinateIndexEquiv d).symm)

/-- The coordinate equivalence is continuous in both directions. -/
def complexModelRealContinuousLinearEquiv (d : ℕ) :
    (Fin d → ℂ) ≃L[ℝ] (Fin (2 * d) → ℝ) :=
  (complexModelRealLinearEquiv d).toContinuousLinearEquiv

@[simp]
theorem complexModelRealContinuousLinearEquiv_apply_re (d : ℕ)
    (z : Fin d → ℂ) (i : Fin d) :
    complexModelRealContinuousLinearEquiv d z
      (complexRealCoordinateIndexEquiv d (Sum.inl i)) = (z i).re := by
  change Sum.elim (fun j => (z j).re) (fun j => (z j).im)
    ((complexRealCoordinateIndexEquiv d).symm
      (complexRealCoordinateIndexEquiv d (Sum.inl i))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp]
theorem complexModelRealContinuousLinearEquiv_apply_im (d : ℕ)
    (z : Fin d → ℂ) (i : Fin d) :
    complexModelRealContinuousLinearEquiv d z
      (complexRealCoordinateIndexEquiv d (Sum.inr i)) = (z i).im := by
  change Sum.elim (fun j => (z j).re) (fun j => (z j).im)
    ((complexRealCoordinateIndexEquiv d).symm
      (complexRealCoordinateIndexEquiv d (Sum.inr i))) = _
  rw [Equiv.symm_apply_apply]
  rfl

@[simp]
theorem complexModelRealContinuousLinearEquiv_symm_apply_re (d : ℕ)
    (x : Fin (2 * d) → ℝ) (i : Fin d) :
    ((complexModelRealContinuousLinearEquiv d).symm x i).re =
      x (complexRealCoordinateIndexEquiv d (Sum.inl i)) := rfl

@[simp]
theorem complexModelRealContinuousLinearEquiv_symm_apply_im (d : ℕ)
    (x : Fin (2 * d) → ℝ) (i : Fin d) :
    ((complexModelRealContinuousLinearEquiv d).symm x i).im =
      x (complexRealCoordinateIndexEquiv d (Sum.inr i)) := rfl

theorem complexModelRealContinuousLinearEquiv_symm_apply (d : ℕ)
    (x : Fin (2 * d) → ℝ) (i : Fin d) :
    (complexModelRealContinuousLinearEquiv d).symm x i =
      (x (complexRealCoordinateIndexEquiv d (Sum.inl i)) : ℂ) +
        (x (complexRealCoordinateIndexEquiv d (Sum.inr i)) : ℂ) * Complex.I :=
  Complex.equivRealProdCLM_symm_apply _

theorem contDiff_complexModelRealCoordinates (d : ℕ) (r : ℕ∞ω) :
    ContDiff ℝ r (complexModelRealContinuousLinearEquiv d) :=
  (complexModelRealContinuousLinearEquiv d).contDiff

theorem contDiff_complexModelRealCoordinates_symm (d : ℕ) (r : ℕ∞ω) :
    ContDiff ℝ r (complexModelRealContinuousLinearEquiv d).symm :=
  (complexModelRealContinuousLinearEquiv d).symm.contDiff

/-- Real coordinates give a diffeomorphism for every smoothness order. -/
def complexModelRealDiffeomorph (d : ℕ) (r : ℕ∞ω) :
    Diffeomorph (𝓘(ℝ, Fin d → ℂ)) (𝓘(ℝ, Fin (2 * d) → ℝ))
      (Fin d → ℂ) (Fin (2 * d) → ℝ) r where
  toEquiv := (complexModelRealContinuousLinearEquiv d).toEquiv
  contMDiff_toFun := (contDiff_complexModelRealCoordinates d r).contMDiff
  contMDiff_invFun := (contDiff_complexModelRealCoordinates_symm d r).contMDiff

@[simp]
theorem complexModelRealDiffeomorph_apply (d : ℕ) (r : ℕ∞ω) (z : Fin d → ℂ) :
    complexModelRealDiffeomorph d r z = complexModelRealContinuousLinearEquiv d z := rfl

@[simp]
theorem complexModelRealDiffeomorph_symm_apply (d : ℕ) (r : ℕ∞ω)
    (x : Fin (2 * d) → ℝ) :
    (complexModelRealDiffeomorph d r).symm x =
      (complexModelRealContinuousLinearEquiv d).symm x := rfl

@[simp]
theorem complexModelRealDiffeomorph_toEquiv (d : ℕ) (r : ℕ∞ω) :
    (complexModelRealDiffeomorph d r).toEquiv =
      (complexModelRealContinuousLinearEquiv d).toEquiv := rfl

@[simp]
theorem complexModelRealDiffeomorph_toHomeomorph (d : ℕ) (r : ℕ∞ω) :
    (complexModelRealDiffeomorph d r).toHomeomorph =
      (complexModelRealContinuousLinearEquiv d).toHomeomorph := rfl

end

end OAI.Topology.Euclidean.ComplexModelRealCoordinates.Globalization
