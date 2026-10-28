import OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne
import OAI.AlgebraicGeometry.ComplexMultiplication.ScalarDescent
import Mathlib.LinearAlgebra.Contraction

/-! # Hom Base Change -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HomBaseChange.CM

noncomputable section

/-!
# Scalar extension of rational linear maps

The canonical map from scalar-extended rational homomorphisms to linear
maps of scalar-extended spaces is an isomorphism when the source is finite
dimensional. Its construction uses the actual base-change map, and scalar
Galois conjugation acts by conjugating its input and output coefficients.
-/

open scoped TensorProduct

variable (K : Type*) [Field K] [Algebra ℚ K]
variable (U V : Type*) [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]

/-- The canonical scalar extension of the rational Hom space. -/
def homBaseChange : K ⊗[ℚ] (U →ₗ[ℚ] V) →ₗ[K] (K ⊗[ℚ] U →ₗ[K] K ⊗[ℚ] V) :=
  (LinearMap.baseChangeHom ℚ K U V).liftBaseChange K

@[simp]
theorem homBaseChange_tmul (a : K) (f : U →ₗ[ℚ] V) :
    homBaseChange K U V (a ⊗ₜ[ℚ] f) = a • f.baseChange K := rfl

@[simp]
theorem homBaseChange_tmul_apply (a b : K) (f : U →ₗ[ℚ] V) (u : U) :
    homBaseChange K U V (a ⊗ₜ[ℚ] f) (b ⊗ₜ[ℚ] u) = (a * b) ⊗ₜ[ℚ] f u := by
  simp [TensorProduct.smul_tmul', smul_eq_mul]

section FiniteSource

variable [FiniteDimensional ℚ U]

/-- Evaluation on rational vectors agrees with the standard tensor-Hom equivalence. -/
theorem homBaseChange_apply_one (x : K ⊗[ℚ] (U →ₗ[ℚ] V)) (u : U) :
    homBaseChange K U V x ((1 : K) ⊗ₜ[ℚ] u) = lTensorHomEquivHomLTensor ℚ U K V x u := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul a f => simp [TensorProduct.smul_tmul', smul_eq_mul]

/-- Extending scalars commutes with Hom when the rational source is finite dimensional. -/
theorem homBaseChange_bijective : Function.Bijective (homBaseChange K U V) := by
  constructor
  · intro x y h
    apply (lTensorHomEquivHomLTensor ℚ U K V).injective
    apply LinearMap.ext
    intro u
    simpa only [homBaseChange_apply_one] using
      congrArg (fun f : K ⊗[ℚ] U →ₗ[K] K ⊗[ℚ] V => f ((1 : K) ⊗ₜ[ℚ] u)) h
  · intro f
    let f₀ : U →ₗ[ℚ] K ⊗[ℚ] V :=
      (f.restrictScalars ℚ).comp (TensorProduct.mk ℚ K U 1)
    let x := (lTensorHomEquivHomLTensor ℚ U K V).symm f₀
    refine ⟨x, ?_⟩
    apply LinearMap.ext
    intro y
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul a u =>
      have hu : homBaseChange K U V x ((1 : K) ⊗ₜ[ℚ] u) = f ((1 : K) ⊗ₜ[ℚ] u) := by
        rw [homBaseChange_apply_one]
        exact congrArg (fun l : U →ₗ[ℚ] K ⊗[ℚ] V => l u)
          ((lTensorHomEquivHomLTensor ℚ U K V).apply_symm_apply f₀)
      have ha := congrArg (fun z : K ⊗[ℚ] V => a • z) hu
      simpa only [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using ha

/-- The canonical coefficient comparison for linear maps, with no choice of a Hom basis. -/
def homBaseChangeEquiv : K ⊗[ℚ] (U →ₗ[ℚ] V) ≃ₗ[K] (K ⊗[ℚ] U →ₗ[K] K ⊗[ℚ] V) :=
  LinearEquiv.ofBijective (homBaseChange K U V) (homBaseChange_bijective K U V)

@[simp]
theorem homBaseChangeEquiv_apply (x : K ⊗[ℚ] (U →ₗ[ℚ] V)) :
    homBaseChangeEquiv K U V x = homBaseChange K U V x := rfl

end FiniteSource

/-- Scalar conjugation of a Hom tensor is conjugation on its argument and its value. -/
theorem homBaseChange_scalarConjugate (g : K ≃ₐ[ℚ] K)
    (x : K ⊗[ℚ] (U →ₗ[ℚ] V)) (u : K ⊗[ℚ] U) :
    homBaseChange K U V (ScalarDescent.CM.scalarConjugate ℚ K (U →ₗ[ℚ] V) g x)
        (ScalarDescent.CM.scalarConjugate ℚ K U g u) =
      ScalarDescent.CM.scalarConjugate ℚ K V g (homBaseChange K U V x u) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul a f =>
    induction u using TensorProduct.inductionOn with
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul b u => simp [TensorProduct.smul_tmul', smul_eq_mul]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HomBaseChange.CM
