import Mathlib.LinearAlgebra.Isomorphisms

/-! # Linear Quotient Dual -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LinearQuotientDual.Cycles

noncomputable section

/-!
# Linear maps on a quotient and the annihilator of its kernel

For a surjective linear map `q`, precomposition with `q` identifies linear maps
out of its codomain with linear maps on its domain that vanish on `ker q`.
The inverse is the native quotient lift transported along the first
isomorphism theorem. The coefficient module is arbitrary.
-/

universe uR uV uW uM

variable {R : Type uR} [CommRing R]
variable {V : Type uV} [AddCommGroup V] [Module R V]
variable {W : Type uW} [AddCommGroup W] [Module R W]

/-- The coefficient-valued linear maps that vanish on the kernel of `q`. -/
def kernelAnnihilator (q : V →ₗ[R] W) (M : Type uM)
    [AddCommGroup M] [Module R M] : Submodule R (V →ₗ[R] M) where
  carrier := {φ | q.ker ≤ φ.ker}
  zero_mem' := by
    intro v _
    rfl
  add_mem' := by
    intro φ ψ hφ hψ v hv
    change φ v + ψ v = 0
    rw [hφ hv, hψ hv, add_zero]
  smul_mem' := by
    intro r φ hφ v hv
    change r • φ v = 0
    rw [hφ hv, smul_zero]

variable {M : Type uM} [AddCommGroup M] [Module R M]

@[simp]
theorem mem_kernelAnnihilator (q : V →ₗ[R] W) (φ : V →ₗ[R] M) :
    φ ∈ kernelAnnihilator q M ↔ q.ker ≤ φ.ker :=
  Iff.rfl

private def kernelAnnihilatorLift (q : V →ₗ[R] W) (hq : Function.Surjective q)
    (φ : kernelAnnihilator q M) : W →ₗ[R] M :=
  (q.ker.liftQ φ.val φ.property).comp (q.quotKerEquivOfSurjective hq).symm.toLinearMap

private theorem kernelAnnihilatorLift_apply (q : V →ₗ[R] W)
    (hq : Function.Surjective q) (φ : kernelAnnihilator q M) (v : V) :
    kernelAnnihilatorLift q hq φ (q v) = φ.val v := by
  change (q.ker.liftQ φ.val φ.property)
    ((q.quotKerEquivOfSurjective hq).symm (q v)) = φ.val v
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

/-- Precomposition with a surjection identifies maps out of its codomain with
the linear maps on its domain that vanish on its kernel. -/
def quotientDualEquiv (q : V →ₗ[R] W) (hq : Function.Surjective q) :
    (W →ₗ[R] M) ≃ₗ[R] kernelAnnihilator q M where
  toFun φ := ⟨φ.comp q, by
    intro v hv
    change φ (q v) = 0
    rw [show q v = 0 from hv, map_zero]⟩
  invFun := kernelAnnihilatorLift q hq
  left_inv φ := by
    ext w
    obtain ⟨v, rfl⟩ := hq w
    exact kernelAnnihilatorLift_apply q hq _ v
  right_inv φ := by
    apply Subtype.ext
    ext v
    exact kernelAnnihilatorLift_apply q hq φ v
  map_add' φ ψ := by
    apply Subtype.ext
    ext v
    rfl
  map_smul' r φ := by
    apply Subtype.ext
    ext v
    rfl

@[simp]
theorem quotientDualEquiv_apply_val (q : V →ₗ[R] W) (hq : Function.Surjective q)
    (φ : W →ₗ[R] M) :
    (quotientDualEquiv q hq φ).val = φ.comp q :=
  rfl

@[simp]
theorem quotientDualEquiv_apply (q : V →ₗ[R] W) (hq : Function.Surjective q)
    (φ : W →ₗ[R] M) (v : V) :
    (quotientDualEquiv q hq φ).val v = φ (q v) :=
  rfl

/-- The inverse is the quotient lift followed by the inverse of the native
first-isomorphism equivalence. -/
theorem quotientDualEquiv_symm_eq_liftQ (q : V →ₗ[R] W)
    (hq : Function.Surjective q) (φ : kernelAnnihilator q M) :
    (quotientDualEquiv q hq).symm φ =
      (q.ker.liftQ φ.val φ.property).comp
        (q.quotKerEquivOfSurjective hq).symm.toLinearMap :=
  rfl

@[simp]
theorem quotientDualEquiv_symm_apply (q : V →ₗ[R] W)
    (hq : Function.Surjective q) (φ : kernelAnnihilator q M) (v : V) :
    (quotientDualEquiv q hq).symm φ (q v) = φ.val v :=
  kernelAnnihilatorLift_apply q hq φ v

@[simp]
theorem quotientDualEquiv_symm_comp (q : V →ₗ[R] W)
    (hq : Function.Surjective q) (φ : kernelAnnihilator q M) :
    ((quotientDualEquiv q hq).symm φ).comp q = φ.val := by
  ext v
  exact quotientDualEquiv_symm_apply q hq φ v

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LinearQuotientDual.Cycles
