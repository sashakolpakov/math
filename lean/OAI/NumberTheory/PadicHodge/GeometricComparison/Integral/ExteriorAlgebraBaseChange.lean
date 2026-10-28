import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Exterior Algebra Base Change -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ExteriorAlgebraBaseChange.IntegralExteriorBaseChange

noncomputable section

/-! Exterior algebra commutes with coefficient extension over every commutative ring. -/

open scoped TensorProduct

variable (R S M : Type*) [CommRing R] [CommRing S] [AddCommGroup M]
  [Algebra R S] [Module R M]

def ofBaseChangeAux : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra S (S ⊗[R] M) :=
  ExteriorAlgebra.lift R ⟨(ExteriorAlgebra.ι S).restrictScalars R ∘ₗ TensorProduct.mk R S M 1,
    fun m => ExteriorAlgebra.ι_sq_zero (1 ⊗ₜ[R] m)⟩

theorem ofBaseChangeAux_ι (m : M) :
    ofBaseChangeAux R S M (ExteriorAlgebra.ι R m) = ExteriorAlgebra.ι S (1 ⊗ₜ[R] m) :=
  ExteriorAlgebra.lift_ι_apply _ _ _ _

def ofBaseChange : S ⊗[R] ExteriorAlgebra R M →ₐ[S] ExteriorAlgebra S (S ⊗[R] M) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (ofBaseChangeAux R S M)
    (fun _ _ => Algebra.commutes _ _)

theorem ofBaseChange_tmul_ι (s : S) (m : M) :
    ofBaseChange R S M (s ⊗ₜ[R] ExteriorAlgebra.ι R m) = ExteriorAlgebra.ι S (s ⊗ₜ[R] m) := by
  change algebraMap _ _ s * ofBaseChangeAux R S M (ExteriorAlgebra.ι R m) = _
  rw [ofBaseChangeAux_ι, ← Algebra.smul_def, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

def tensorIota : S ⊗[R] M →ₗ[S] S ⊗[R] ExteriorAlgebra R M :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id : S →ₗ[S] S) (ExteriorAlgebra.ι R)

theorem tensorIota_tmul (s : S) (m : M) :
    tensorIota R S M (s ⊗ₜ[R] m) = s ⊗ₜ[R] ExteriorAlgebra.ι R m := rfl

theorem tensorIota_skew (x y : S ⊗[R] M) :
    tensorIota R S M x * tensorIota R S M y + tensorIota R S M y * tensorIota R S M x = 0 := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz =>
    simp only [map_add, add_mul, mul_add]
    calc
      _ = (tensorIota R S M x * tensorIota R S M y + tensorIota R S M y * tensorIota R S M x) +
          (tensorIota R S M z * tensorIota R S M y + tensorIota R S M y * tensorIota R S M z) := by abel
      _ = 0 := by rw [hx, hz, add_zero]
  | tmul s m =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz =>
      simp only [map_add, add_mul, mul_add]
      calc
        _ = (tensorIota R S M (s ⊗ₜ[R] m) * tensorIota R S M y +
            tensorIota R S M y * tensorIota R S M (s ⊗ₜ[R] m)) +
            (tensorIota R S M (s ⊗ₜ[R] m) * tensorIota R S M z +
            tensorIota R S M z * tensorIota R S M (s ⊗ₜ[R] m)) := by abel
        _ = 0 := by rw [hy, hz, add_zero]
    | tmul t n =>
      rw [tensorIota_tmul, tensorIota_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, mul_comm t s, ← TensorProduct.tmul_add]
      rw [show ExteriorAlgebra.ι R m * ExteriorAlgebra.ι R n +
          ExteriorAlgebra.ι R n * ExteriorAlgebra.ι R m = 0 by
        simp]
      exact TensorProduct.tmul_zero _ _

theorem tensorIota_square (x : S ⊗[R] M) : tensorIota R S M x * tensorIota R S M x = 0 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, add_mul, mul_add, hx, hy, zero_add, add_zero]
    exact tensorIota_skew R S M y x
  | tmul s m =>
    rw [tensorIota_tmul, Algebra.TensorProduct.tmul_mul_tmul, ExteriorAlgebra.ι_sq_zero,
      TensorProduct.tmul_zero]

def toBaseChange : ExteriorAlgebra S (S ⊗[R] M) →ₐ[S] S ⊗[R] ExteriorAlgebra R M :=
  ExteriorAlgebra.lift S ⟨tensorIota R S M, tensorIota_square R S M⟩

theorem toBaseChange_ι (x : S ⊗[R] M) :
    toBaseChange R S M (ExteriorAlgebra.ι S x) = tensorIota R S M x :=
  ExteriorAlgebra.lift_ι_apply _ _ _ _

theorem toBaseChange_comp_ofBaseChange :
    (toBaseChange R S M).comp (ofBaseChange R S M) = AlgHom.id _ _ := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · apply ExteriorAlgebra.hom_ext
    ext m
    change toBaseChange R S M (ofBaseChange R S M (1 ⊗ₜ[R] ExteriorAlgebra.ι R m)) =
      1 ⊗ₜ[R] ExteriorAlgebra.ι R m
    rw [ofBaseChange_tmul_ι, toBaseChange_ι, tensorIota_tmul]

theorem ofBaseChange_comp_toBaseChange :
    (ofBaseChange R S M).comp (toBaseChange R S M) = AlgHom.id _ _ := by
  apply ExteriorAlgebra.hom_ext
  apply TensorProduct.AlgebraTensorModule.ext
  intro s m
  change ofBaseChange R S M (toBaseChange R S M (ExteriorAlgebra.ι S (s ⊗ₜ[R] m))) =
    ExteriorAlgebra.ι S (s ⊗ₜ[R] m)
  rw [toBaseChange_ι, tensorIota_tmul, ofBaseChange_tmul_ι]

def algebraEquiv : S ⊗[R] ExteriorAlgebra R M ≃ₐ[S] ExteriorAlgebra S (S ⊗[R] M) :=
  AlgEquiv.ofAlgHom (ofBaseChange R S M) (toBaseChange R S M)
    (ofBaseChange_comp_toBaseChange R S M) (toBaseChange_comp_ofBaseChange R S M)

theorem algebraEquiv_tmul_ι (s : S) (m : M) :
    algebraEquiv R S M (s ⊗ₜ[R] ExteriorAlgebra.ι R m) = ExteriorAlgebra.ι S (s ⊗ₜ[R] m) :=
  ofBaseChange_tmul_ι R S M s m

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ExteriorAlgebraBaseChange.IntegralExteriorBaseChange
