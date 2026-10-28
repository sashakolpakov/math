import OAI.AlgebraicGeometry.ComplexMultiplication.Hodge.Retract
import OAI.AlgebraicGeometry.ComplexMultiplication.DiagonalAction
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # Field Product Components -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.FieldProductComponents

noncomputable section

section

/-! # The internal CM decomposition of a rank-one field-product representation -/

open scoped TensorProduct DirectSum

variable {U : Type*} [AddCommGroup U] [Module ℚ U]
variable {n : ℕ} (K : Fin n → Type) [∀ i, Field (K i)]
  [∀ i, Algebra ℚ (K i)]
  (e : U ≃ₗ[ℚ] ((i : Fin n) → K i))

/-- Include a field factor by its actual coordinate in the supplied rational model. -/
def cmCoordinateInclusion (i : Fin n) : K i →ₗ[ℚ] U :=
  e.symm.toLinearMap.comp (LinearMap.single ℚ K i)

/-- The actual rational subspace corresponding to one field factor. -/
def cmCoordinateSubspace (i : Fin n) : Submodule ℚ U :=
  LinearMap.range (cmCoordinateInclusion K e i)

theorem cmCoordinateInclusion_injective (i : Fin n) :
    Function.Injective (cmCoordinateInclusion K e i) := by
  intro a b h
  have he := congrArg (fun u => e u i) h
  simpa [cmCoordinateInclusion] using he

/-- The coordinate subspace is rationally isomorphic to its original CM field. -/
def cmCoordinateFieldEquiv (i : Fin n) : cmCoordinateSubspace K e i ≃ₗ[ℚ] K i :=
  (LinearEquiv.ofInjective (cmCoordinateInclusion K e i)
    (cmCoordinateInclusion_injective K e i)).symm

/-- Project onto the coordinate subspace by taking its field coordinate. -/
def cmCoordinateRetract (i : Fin n) : U →ₗ[ℚ] cmCoordinateSubspace K e i :=
  (cmCoordinateInclusion K e i).rangeRestrict.comp
    ((LinearMap.proj i).comp e.toLinearMap)

theorem cmCoordinateRetract_subtype (i : Fin n) :
    (cmCoordinateRetract K e i).comp (cmCoordinateSubspace K e i).subtype = LinearMap.id := by
  ext u
  obtain ⟨a, ha⟩ := u.property
  change cmCoordinateInclusion K e i (e u.val i) = u.val
  rw [← ha]
  simp [cmCoordinateInclusion]

theorem cmCoordinateProjection_eq_diagonal (i : Fin n) :
    (cmCoordinateSubspace K e i).subtype.comp (cmCoordinateRetract K e i) =
      Definitions.diagonalAction K e (Pi.single i 1) := by
  ext u
  apply e.injective
  change e (e.symm (Pi.single i (e u i))) = e (Definitions.diagonalAction K e (Pi.single i 1) u)
  rw [LinearEquiv.apply_symm_apply]
  rw [← DiagonalAction.diagonalActionAlgHom_apply, DiagonalAction.model_diagonalAction]
  ext j
  by_cases h : j = i
  · subst j
    simp
  · simp [Pi.single_eq_of_ne h]

variable (H : WeightOne.CM.WeightOneHodgeStructure U)
  (h : ∀ a, WeightOne.CM.IsHodgeMap H H (Definitions.diagonalAction K e a))

/-- Each actual coordinate subspace inherits the original geometric Hodge types. -/
def cmCoordinateHodge (i : Fin n) : WeightOne.CM.WeightOneHodgeStructure (cmCoordinateSubspace K e i) :=
  Hodge.Retract.hodgeRetract H (cmCoordinateSubspace K e i) (cmCoordinateRetract K e i)
    (cmCoordinateRetract_subtype K e i)
    ((cmCoordinateProjection_eq_diagonal K e i).symm ▸ h (Pi.single i 1))

/-- The actual inclusion of each coordinate subspace is a Hodge map. -/
theorem cmCoordinate_inclusion_hodge (i : Fin n) :
    WeightOne.CM.IsHodgeMap (cmCoordinateHodge K e H h i) H (cmCoordinateSubspace K e i).subtype :=
  Hodge.Retract.hodgeRetract_inclusion H _ _ _ _

end

/-! # Rank-one CM field actions on the actual coordinate Hodge subspaces -/

open scoped TensorProduct DirectSum

variable {U : Type*} [AddCommGroup U] [Module ℚ U]
variable {n : ℕ} (K : Fin n → Type) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
  (e : U ≃ₗ[ℚ] ((i : Fin n) → K i))

theorem cmCoordinateFieldEquiv_symm_subtype (i : Fin n) (a : K i) :
    ((cmCoordinateFieldEquiv K e i).symm a : U) = cmCoordinateInclusion K e i a := rfl

theorem cmCoordinateFieldEquiv_apply (i : Fin n) (u : cmCoordinateSubspace K e i) :
    cmCoordinateFieldEquiv K e i u = e u.val i := by
  obtain ⟨a, rfl⟩ := (cmCoordinateFieldEquiv K e i).symm.surjective u
  rw [LinearEquiv.apply_symm_apply, cmCoordinateFieldEquiv_symm_subtype]
  simp [cmCoordinateInclusion]

local instance cmCoordinateModule (i : Fin n) : Module (K i) (cmCoordinateSubspace K e i) :=
  (cmCoordinateFieldEquiv K e i).toAddEquiv.module (K i)

local instance cmCoordinateScalarTower (i : Fin n) :
    IsScalarTower ℚ (K i) (cmCoordinateSubspace K e i) :=
  (cmCoordinateFieldEquiv K e i).isScalarTower (A := K i)

theorem cmCoordinate_scalar_inclusion (i : Fin n) (a : K i)
    (u : cmCoordinateSubspace K e i) :
    (a • u : cmCoordinateSubspace K e i).val = Definitions.diagonalAction K e (Pi.single i a) u.val := by
  change ((cmCoordinateFieldEquiv K e i).symm
    (a • cmCoordinateFieldEquiv K e i u) : U) = _
  rw [cmCoordinateFieldEquiv_symm_subtype, cmCoordinateFieldEquiv_apply]
  apply e.injective
  change e (e.symm (Pi.single i (a * e u.val i))) =
    e (Definitions.diagonalAction K e (Pi.single i a) u.val)
  rw [LinearEquiv.apply_symm_apply]
  rw [← DiagonalAction.diagonalActionAlgHom_apply, DiagonalAction.model_diagonalAction]
  ext j
  by_cases h : j = i
  · subst j
    simp
  · simp [Pi.single_eq_of_ne h]

theorem cmCoordinate_scalar_intertwines (i : Fin n) (a : K i) :
    (cmCoordinateSubspace K e i).subtype.comp (WeightOne.CM.scalarEndomorphism (K i) a) =
      (Definitions.diagonalAction K e (Pi.single i a)).comp (cmCoordinateSubspace K e i).subtype := by
  ext u
  exact cmCoordinate_scalar_inclusion K e i a u

variable (H : WeightOne.CM.WeightOneHodgeStructure U)
  (h : ∀ a, WeightOne.CM.IsHodgeMap H H (Definitions.diagonalAction K e a))

theorem cmCoordinate_scalar_hodge (i : Fin n) (a : K i) :
    WeightOne.CM.IsHodgeMap (cmCoordinateHodge K e H h i) (cmCoordinateHodge K e H h i)
      (WeightOne.CM.scalarEndomorphism (K i) a) := by
  intro x hx
  let j := (cmCoordinateSubspace K e i).subtype
  change j.baseChange ℂ ((WeightOne.CM.scalarEndomorphism (K i) a).baseChange ℂ x) ∈ H.holomorphic
  have he := congrArg (fun f => f.baseChange ℂ x) (cmCoordinate_scalar_intertwines K e i a)
  simp only [LinearMap.baseChange_comp, LinearMap.comp_apply] at he
  rw [he]
  exact h (Pi.single i a) (j.baseChange ℂ x) hx

variable [∀ i, NumberField.IsCMField (K i)]

/-- The actual field coordinate gives rank one and preserves the induced geometric Hodge type. -/
def cmProductComponent (i : Fin n) : Decomposition.CM.CMComponent H where
  subspace := cmCoordinateSubspace K e i
  hodge := cmCoordinateHodge K e H h i
  inclusion_hodge := cmCoordinate_inclusion_hodge K e H h i
  field := K i
  scalarAction := cmCoordinateModule K e i
  scalarTower := cmCoordinateScalarTower K e i
  cm :=
    { rank_one := by
        let f := (cmCoordinateFieldEquiv K e i).toAddEquiv.linearEquiv (K i)
        exact f.finrank_eq.trans (Module.finrank_self (K i))
      hodge_action := cmCoordinate_scalar_hodge K e H h i }

end

end OAI.AlgebraicGeometry.ComplexMultiplication.FieldProductComponents
