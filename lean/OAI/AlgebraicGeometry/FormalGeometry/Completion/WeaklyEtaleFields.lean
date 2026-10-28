import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Weakly Etale Fields -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.WeaklyEtaleFields.Construction

noncomputable section

/-!
# Completion: algebraicity of fields with flat diagonal

This supplies a ring-theoretic step toward acyclicity of the geometric point
on the pro-étale site. A transcendental element would make evaluation from a
polynomial ring flat after base change and composition with the diagonal.
Evaluation at a field element cannot be flat.
-/

open scoped TensorProduct _root_.Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Evaluation of a polynomial ring in its coefficient field is not flat. -/
theorem polynomial_aeval_not_flat (x : L) :
    ¬ (Polynomial.aeval x : L[X] →ₐ[L] L).toRingHom.Flat := by
  intro h
  let φ := (Polynomial.aeval x : L[X] →ₐ[L] L).toRingHom
  let : Algebra L[X] L := φ.toAlgebra
  have : Module.Flat L[X] L := h
  have hi : Function.Injective φ := FaithfulSMul.algebraMap_injective L[X] L
  have he : φ (Polynomial.X - Polynomial.C x) = φ 0 := by simp [φ]
  have hz : (Polynomial.X - Polynomial.C x : L[X]) = 0 := hi he
  exact Polynomial.X_sub_C_ne_zero x hz

/-- A field extension whose diagonal is flat is algebraic. -/
theorem isAlgebraic_of_flat_diagonal
    (hdiag : (Algebra.TensorProduct.lmul' K : L ⊗[K] L →ₐ[K] L).toRingHom.Flat) :
    Algebra.IsAlgebraic K L := by
  constructor
  intro x
  by_contra hx
  let φ : K[X] →ₐ[K] L := Polynomial.aeval x
  have hφ : φ.toRingHom.Flat := by
    let : Algebra K[X] L := φ.toRingHom.toAlgebra
    have : FaithfulSMul K[X] L := (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (transcendental_iff_injective.mp hx)
    have : Module.IsTorsionFree K[X] L := inferInstance
    exact (inferInstance : Module.Flat K[X] L)
  let e : L[X] ≃ₐ[L] L ⊗[K] K[X] := polyEquivTensor' K L
  have heval : ((Algebra.TensorProduct.lmul' K : L ⊗[K] L →ₐ[K] L).toRingHom.comp
      (Algebra.TensorProduct.lTensor (S := K) L φ).toRingHom).comp e.toRingHom =
        (Polynomial.aeval x : L[X] →ₐ[L] L).toRingHom := by
    ext a <;> simp [e, φ]
  apply polynomial_aeval_not_flat x
  rw [← heval]
  exact ((RingHom.Flat.of_bijective e.bijective).comp (hφ.lTensor (S := K) L)).comp hdiag

/-- Over an algebraically closed field, a field extension with flat diagonal
is the base field. -/
theorem algebraMap_bijective_of_flat_diagonal [IsAlgClosed K]
    (hdiag : (Algebra.TensorProduct.lmul' K : L ⊗[K] L →ₐ[K] L).toRingHom.Flat) :
    Function.Bijective (algebraMap K L) := by
  have : Algebra.IsAlgebraic K L := isAlgebraic_of_flat_diagonal hdiag
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.WeaklyEtaleFields.Construction
