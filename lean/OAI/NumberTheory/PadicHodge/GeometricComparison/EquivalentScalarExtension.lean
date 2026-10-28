import OAI.NumberTheory.PadicHodge.GeometricComparison.SemilinearCharpolyTo

/-! # Equivalent Scalar Extension -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.EquivalentScalarExtension.ScalarExtension

noncomputable section

/-! Scalar extension along an actual field equivalence is a semilinear equivalence. -/

open scoped TensorProduct

variable {R S : Type*} [Field R] [Field S] [Algebra R S]
  (σ : R ≃+* S) (hσ : algebraMap R S = σ.toRingHom)
  (V : Type*) [AddCommGroup V] [Module R V]

def unitMap : V →ₛₗ[σ.toRingHom] (S ⊗[R] V) where
  toFun v := 1 ⊗ₜ[R] v
  map_add' v w := TensorProduct.tmul_add 1 v w
  map_smul' r v := by
    change 1 ⊗ₜ[R] (r • v) = σ r • (1 ⊗ₜ[R] v)
    have hr : σ r = algebraMap R S r := (DFunLike.congr_fun hσ r).symm
    rw [hr, IsScalarTower.algebraMap_smul, TensorProduct.tmul_smul]

theorem unitMap_bijective : Function.Bijective (unitMap σ hσ V) := by
  constructor
  · exact Module.Flat.tensorProduct_mk_injective (R := R) (S := S) (M := V)
  · intro x
    induction x using TensorProduct.inductionOn with
    | tmul a v =>
        obtain ⟨r, rfl⟩ := σ.surjective a
        refine ⟨r • v, ?_⟩
        rw [(unitMap σ hσ V).map_smulₛₗ]
        change σ r • (1 ⊗ₜ[R] v) = σ r ⊗ₜ[R] v
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy =>
        obtain ⟨v, rfl⟩ := hx
        obtain ⟨w, rfl⟩ := hy
        exact ⟨v + w, (unitMap σ hσ V).map_add v w⟩

def equiv : V ≃ₛₗ[σ.toRingHom] (S ⊗[R] V) :=
  LinearEquiv.ofBijective (unitMap σ hσ V) (unitMap_bijective σ hσ V)

theorem equiv_apply (v : V) : equiv σ hσ V v = 1 ⊗ₜ[R] v := rfl

theorem equiv_naturality {W : Type*} [AddCommGroup W] [Module R W]
    (f : V →ₗ[R] W) (v : V) :
    equiv σ hσ W (f v) = f.baseChange S (equiv σ hσ V v) := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.EquivalentScalarExtension.ScalarExtension
