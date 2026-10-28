import OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialIntegration
import OAI.NumberTheory.ArithmeticGroups.Lattices.SolvableLiePreservers

/-! # Matrix Invariant Exponential -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixInvariantExponential.Construction

noncomputable section

section

/-! Matrix exponentials preserve every invariant linear subspace. -/

open scoped Classical _root_.Matrix.Norms.Operator
open NormedSpace Set

variable {k : Type} [RCLike k] {n : ℕ}

def matrixInvariantSubalgebra (W : Submodule k (Fin n → k)) :
    Subalgebra k (Matrix (Fin n) (Fin n) k) where
  carrier := {A | ∀ x ∈ W, A.mulVec x ∈ W}
  add_mem' hA hB x hx := by
    rw [Matrix.add_mulVec]
    exact W.add_mem (hA x hx) (hB x hx)
  mul_mem' hA hB x hx := by
    rw [← Matrix.mulVec_mulVec]
    exact hA _ (hB x hx)
  zero_mem' x _ := by simpa only [Matrix.zero_mulVec] using W.zero_mem
  one_mem' x hx := by simpa only [Matrix.one_mulVec] using hx
  algebraMap_mem' c x hx := by
    simpa only [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec] using W.smul_mem c hx

theorem matrixInvariantSubalgebra_closed (W : Submodule k (Fin n → k)) :
    IsClosed (matrixInvariantSubalgebra W : Set (Matrix (Fin n) (Fin n) k)) := by
  change IsClosed {A : Matrix (Fin n) (Fin n) k | ∀ x ∈ W, A.mulVec x ∈ W}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro _
  exact W.closed_of_finiteDimensional.preimage (by fun_prop)

theorem matrix_exponential_preserves_subspace
    (W : Submodule k (Fin n → k)) {A : Matrix (Fin n) (Fin n) k}
    (hA : ∀ x ∈ W, A.mulVec x ∈ W) (t : k) :
    ∀ x ∈ W, (exp (t • A)).mulVec x ∈ W := by
  have hsmul : t • A ∈ matrixInvariantSubalgebra W :=
    (matrixInvariantSubalgebra W).smul_mem hA t
  exact NormedSpace.exp_mem (R := k) (matrixInvariantSubalgebra_closed W) hsmul

end

/-! A solvable complex matrix Lie algebra generates a solvable subgroup
through the actual matrix exponential. -/

open scoped Classical _root_.Matrix.Norms.Operator
open NormedSpace Set

attribute [local instance] LieRing.ofAssociativeRing

variable {n : ℕ}

def matrixLieRepresentation (S : LieSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) :
    S →ₗ⁅ℂ⁆ Module.End ℂ (Fin n → ℂ) :=
  lieEquivMatrix'.symm.toLieHom.comp S.incl

local instance exponentialLieRingModule (S : LieSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) :
    LieRingModule S (Fin n → ℂ) :=
  LieRingModule.compLieHom (Fin n → ℂ) (matrixLieRepresentation S)

local instance exponentialLieModule (S : LieSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) :
    LieModule ℂ S (Fin n → ℂ) :=
  LieModule.compLieHom (Fin n → ℂ) (matrixLieRepresentation S)

def exponentialGeneratedSubgroup (G : Algebraic.MatrixAlgebraicGroup ℂ n)
    (S : LieSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) (hS : S ≤ Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    Subgroup G.RationalPoints :=
  Subgroup.closure (range (fun A : S => ExponentialIntegration.Construction.infinitesimalExponential G ⟨A.val, hS A.property⟩ 1))

theorem exponentialGeneratedSubgroup_solvable (G : Algebraic.MatrixAlgebraicGroup ℂ n)
    (S : LieSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) (hS : S ≤ Infinitesimal.Action.Construction.infinitesimalStabilizer G)
    [LieAlgebra.IsSolvable S] : Group.IsSolvable (exponentialGeneratedSubgroup G S hS) := by
  let ρ : G.RationalPoints →* ((Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ)) :=
    Matrix.SpecialLinearGroup.toLin'.comp (G.subgroup ℂ (RingHom.id ℂ)).subtype
  have hinj : Function.Injective ρ :=
    Matrix.SpecialLinearGroup.toLin'_injective.comp Subtype.val_injective
  let H := exponentialGeneratedSubgroup G S hS
  apply SolvableLiePreservers.Construction.group_solvable_of_preserves_lie_submodules (L := S) (ρ.comp H.subtype)
    (hinj.comp H.subtype_injective)
  intro W g x hx
  have hle : H ≤ SubmoduleOrbit.Construction.submoduleImageStabilizer ρ W.toSubmodule := by
    change Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨A, rfl⟩
    change W.toSubmodule.map (ρ (ExponentialIntegration.Construction.infinitesimalExponential G ⟨A.val, hS A.property⟩ 1)).toLinearMap = W.toSubmodule
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨y, hy, rfl⟩
      change (exp ((1 : ℂ) • A.val)).mulVec y ∈ W
      apply matrix_exponential_preserves_subspace W.toSubmodule (t := 1) _ y hy
      intro z hz
      exact W.lie_mem hz (x := A)
    · exact LinearEquiv.finrank_map_eq _ _
  have hg := hle g.property
  change W.toSubmodule.map (ρ g.val).toLinearMap = W.toSubmodule at hg
  change ρ g.val x ∈ W.toSubmodule
  rw [← hg]
  exact ⟨x, hx, rfl⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixInvariantExponential.Construction
