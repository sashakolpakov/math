import OAI.Analysis.Schwartz.TensorDecomposition

/-! # Restricted Positions -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RestrictedPositions.CM

noncomputable section

/-! ThetaCycle: finite position coordinates commute with restricted products,
including the actual restricted-product topologies. -/

open scoped Classical
open Filter

variable {I V : Type*} [Finite I] (R : V → Type*) (A : ∀ v, Set (R v))

def restrictedPositionEquiv :
    (I → RestrictedProduct R A cofinite) ≃
      RestrictedProduct (fun v => I → R v) (fun v => {x | ∀ i, x i ∈ A v}) cofinite where
  toFun x := ⟨fun v i => x i v,
    Filter.eventually_all.mpr (fun i => (x i).property)⟩
  invFun x i := ⟨fun v => x v i, x.property.mono (fun _ hv => hv i)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem restricted_position_equiv_apply
    (x : I → RestrictedProduct R A cofinite) (v : V) (i : I) :
    restrictedPositionEquiv R A x v i = x i v := rfl

variable [∀ v, TopologicalSpace (R v)]

theorem restricted_position_equiv_continuous (hA : ∀ v, IsOpen (A v)) :
    Continuous (restrictedPositionEquiv (I := I) R A) := by
  apply (RestrictedProduct.continuous_dom_pi (fun _ v => hA v)).mpr
  intro S hS
  let lift : (I → RestrictedProduct R A (principal S)) →
      RestrictedProduct (fun v => I → R v) (fun v => {x | ∀ i, x i ∈ A v}) (principal S) :=
    fun x => ⟨fun v i => x i v, fun v hv i => (x i).property hv⟩
  have hl : Continuous lift := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    apply continuous_pi
    intro v
    apply continuous_pi
    intro i
    exact (RestrictedProduct.continuous_eval v).comp (continuous_apply i)
  exact (RestrictedProduct.continuous_inclusion hS).comp hl

theorem restricted_position_equiv_symm_continuous :
    Continuous (restrictedPositionEquiv (I := I) R A).symm := by
  apply continuous_pi
  intro i
  apply RestrictedProduct.continuous_dom.mpr
  intro S hS
  let lift : RestrictedProduct (fun v => I → R v)
      (fun v => {x | ∀ j, x j ∈ A v}) (principal S) → RestrictedProduct R A (principal S) :=
    fun x => ⟨fun v => x v i, fun v hv => x.property hv i⟩
  have hl : Continuous lift := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    apply continuous_pi
    intro v
    exact (continuous_apply i).comp (RestrictedProduct.continuous_eval v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hl

def restrictedPositionHomeomorph (hA : ∀ v, IsOpen (A v)) :
    (I → RestrictedProduct R A cofinite) ≃ₜ
      RestrictedProduct (fun v => I → R v) (fun v => {x | ∀ i, x i ∈ A v}) cofinite where
  toEquiv := restrictedPositionEquiv R A
  continuous_toFun := restricted_position_equiv_continuous R A hA
  continuous_invFun := restricted_position_equiv_symm_continuous R A

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RestrictedPositions.CM
