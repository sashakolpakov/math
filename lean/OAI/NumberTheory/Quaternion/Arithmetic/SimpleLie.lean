import OAI.NumberTheory.Quaternion.Arithmetic.TensorInvariantSubspaces
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import OAI.NumberTheory.Quaternion.Arithmetic.LieScalarSimplicity

/-! # Simple Lie -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.SimpleLie

noncomputable section

section

/-! A simple finite-dimensional Lie algebra over an algebraically closed
field remains simple after any field extension. -/

open scoped Classical TensorProduct

variable {k K L : Type*} [Field k] [Field K] [Algebra k K] [LieRing L] [LieAlgebra k L]

theorem tensor_ideal_stable_under_adjoint_algebra
    (I : LieIdeal K (K ⊗[k] L)) {f : Module.End k L} (hf : f ∈ AdjointAssociativeDensity.adjointAssociativeAlgebra k L) :
    ∀ x ∈ I, f.baseChange K x ∈ I := by
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
      obtain ⟨a, rfl⟩ := hf
      intro x hx
      have hm : (LieModule.toEnd K (K ⊗[k] L) (K ⊗[k] L) ((1 : K) ⊗ₜ[k] a)) x ∈ I :=
        I.lie_mem hx
      rwa [LieModule.toEnd_baseChange] at hm
  | algebraMap a =>
      intro x hx
      rw [Algebra.algebraMap_eq_smul_one, LinearMap.baseChange_smul, LinearMap.baseChange_one]
      exact (I.toSubmodule.restrictScalars k).smul_mem a hx
  | add f g _ _ hf hg =>
      intro x hx
      rw [LinearMap.baseChange_add, LinearMap.add_apply]
      exact I.add_mem (hf x hx) (hg x hx)
  | mul f g _ _ hf hg =>
      intro x hx
      rw [LinearMap.baseChange_mul, Module.End.mul_apply]
      exact hf _ (hg x hx)

theorem simple_lie_baseChange_of_algClosed
    [IsAlgClosed k] [FiniteDimensional k L] [LieAlgebra.IsSimple k L] :
    LieAlgebra.IsSimple K (K ⊗[k] L) where
  eq_bot_or_eq_top I := by
    have hstable : ∀ f : Module.End k L, ∀ x ∈ I.toSubmodule, f.baseChange K x ∈ I.toSubmodule := by
      intro f
      apply tensor_ideal_stable_under_adjoint_algebra I
      rw [AdjointAssociativeDensity.adjointAssociativeAlgebra_eq_top]
      trivial
    rcases TensorInvariantSubspaces.tensor_invariant_subspace_eq_bot_or_top I.toSubmodule hstable with hI | hI
    · exact Or.inl (LieSubmodule.toSubmodule_injective hI)
    · exact Or.inr (LieSubmodule.toSubmodule_injective hI)
  non_abelian := by
    intro habel
    let : IsLieAbelian (K ⊗[k] L) := habel
    apply LieAlgebra.IsSimple.non_abelian k (L := L)
    constructor
    intro x y
    have h : ⁅(1 : K) ⊗ₜ[k] x, (1 : K) ⊗ₜ[k] y⁆ = 0 := LieModule.IsTrivial.trivial _ _
    rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul] at h
    exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff (R := k) (M := L) (A := K) ⁅x, y⁆).mp h

end

section

/-! Simplicity descends along field extension and is preserved by Lie
isomorphisms. These results transfer geometric simplicity to the chosen
models of infinitesimal Lie algebras. -/

open scoped TensorProduct

theorem simple_of_LieEquiv
    {k L M : Type*} [CommRing k] [LieRing L] [LieAlgebra k L]
    [LieRing M] [LieAlgebra k M] [LieAlgebra.IsSimple k L]
    (e : L ≃ₗ⁅k⁆ M) : LieAlgebra.IsSimple k M where
  eq_bot_or_eq_top I := by
    rcases LieAlgebra.IsSimple.eq_bot_or_eq_top (LieIdeal.comap e.toLieHom I) with hI | hI
    · left
      apply le_antisymm _ bot_le
      intro x hx
      have hm : e.symm x ∈ LieIdeal.comap e.toLieHom I := by
        change e (e.symm x) ∈ I
        simpa only [e.apply_symm_apply] using hx
      rw [hI, LieSubmodule.mem_bot] at hm
      exact e.symm.injective (hm.trans e.symm.map_zero.symm)
    · right
      apply le_antisymm le_top
      intro x _
      have hm : e.symm x ∈ LieIdeal.comap e.toLieHom I := by rw [hI]; trivial
      change e (e.symm x) ∈ I at hm
      simpa only [e.apply_symm_apply] using hm
  non_abelian := by
    intro hM
    let : IsLieAbelian M := hM
    apply LieAlgebra.IsSimple.non_abelian k (L := L)
    constructor
    intro x y
    apply e.injective
    rw [map_zero, e.toLieHom.map_lie]
    exact LieModule.IsTrivial.trivial _ _

variable {k K L : Type*} [Field k] [Field K] [Algebra k K] [LieRing L] [LieAlgebra k L]

theorem lieAbelian_baseChange [IsLieAbelian L] : IsLieAbelian (K ⊗[k] L) := by
  constructor
  intro x y
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => rw [add_lie, hx, hz, add_zero]
  | tmul a u =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => rw [lie_add, hy, hz, add_zero]
      | tmul b v =>
          rw [LieAlgebra.ExtendScalars.bracket_tmul, LieModule.IsTrivial.trivial,
            TensorProduct.tmul_zero]

theorem lieIdeal_baseChange_injective :
    Function.Injective (fun I : LieIdeal k L => I.baseChange K) := by
  intro I J h
  apply LieSubmodule.toSubmodule_injective
  apply Submodule.baseChange_injective (A := K)
  simpa only [LieSubmodule.coe_baseChange] using congrArg LieSubmodule.toSubmodule h

theorem simple_lie_of_baseChange [LieAlgebra.IsSimple K (K ⊗[k] L)] : LieAlgebra.IsSimple k L where
  eq_bot_or_eq_top I := by
    rcases LieAlgebra.IsSimple.eq_bot_or_eq_top (I.baseChange K) with hI | hI
    · left
      apply lieIdeal_baseChange_injective (K := K)
      simpa only [LieSubmodule.baseChange_bot] using hI
    · right
      apply lieIdeal_baseChange_injective (K := K)
      simpa only [LieSubmodule.baseChange_top] using hI
  non_abelian := by
    intro hL
    let : IsLieAbelian L := hL
    exact LieAlgebra.IsSimple.non_abelian K (L := K ⊗[k] L) (lieAbelian_baseChange (K := K))

end

/-! Restriction of scalars for a Lie subalgebra, with simplicity
transported to the resulting subtype. -/

variable {κ K A : Type*} [CommRing κ] [CommRing K] [Algebra κ K]
  [LieRing A] [LieAlgebra κ A] [LieAlgebra K A] [IsScalarTower κ K A]

def lieSubalgebraRestrictScalars (B : LieSubalgebra K A) : LieSubalgebra κ A :=
  { B.toSubmodule.restrictScalars κ with lie_mem' := B.lie_mem }

theorem lieSubalgebraRestrictScalars_isSimple (B : LieSubalgebra K A)
    [LieAlgebra.IsSimple K B] : LieAlgebra.IsSimple κ (lieSubalgebraRestrictScalars (κ := κ) B) := by
  let : LieAlgebra κ B := {
    lie_smul := fun c x y => Subtype.ext (lie_smul c x.val y.val) }
  let : LieAlgebra.IsSimple κ B := LieScalarSimplicity.isSimple_of_simple_coefficients (K := K)
  let e : B ≃ₗ⁅κ⁆ lieSubalgebraRestrictScalars (κ := κ) B := {
    toFun := fun x => ⟨x.val, x.property⟩
    invFun := fun x => ⟨x.val, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    map_lie' := rfl }
  exact simple_of_LieEquiv e

end

end OAI.NumberTheory.Quaternion.Arithmetic.SimpleLie
