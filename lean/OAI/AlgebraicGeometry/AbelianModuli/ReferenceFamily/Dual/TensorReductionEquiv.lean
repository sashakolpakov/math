import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorReduction
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Tensor Reduction Equiv -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorReductionEquiv

noncomputable section

section

/-! The reduction of a dual-number product is canonically its original
coefficient algebra, with the complete dual-number base action retained. -/

open scoped TensorProduct

variable (k A : Type*) [CommRing k] [CommRing A] [Algebra k A]

local instance : CommRing (DualNumber k ⊗[k] A) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := A)

theorem dualTensorReductionIdeal_eq_map :
    TensorReduction.dualTensorReductionIdeal k A =
      ((TensorReduction.dualScalarReductionIdeal k).map (algebraMap (DualNumber k) (DualNumber k ⊗[k] A)) :
        Ideal (DualNumber k ⊗[k] A)) := rfl

def dualTensorReductionQuotientEquiv :
    ((DualNumber k ⊗[k] A) ⧸ TensorReduction.dualTensorReductionIdeal k A) ≃ₐ[k] A :=
  (Ideal.quotientEquivAlgOfEq k (TensorReduction.dualTensorReduction_ker k A).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (TensorReduction.dualTensorReduction_surjective k A))

theorem dualTensorReductionQuotientEquiv_mk (u : DualNumber k ⊗[k] A) :
    dualTensorReductionQuotientEquiv k A
      (Ideal.Quotient.mk (TensorReduction.dualTensorReductionIdeal k A) u) = TensorReduction.dualTensorReduction k A u := by
  rw [dualTensorReductionQuotientEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]

theorem dualTensorReduction_algebraMap (c : DualNumber k) :
    TensorReduction.dualTensorReduction k A (algebraMap (DualNumber k) (DualNumber k ⊗[k] A) c) =
      algebraMap k A c.fst := by
  change TensorReduction.dualTensorReduction k A (c ⊗ₜ[k] (1 : A)) = _
  rw [TensorReduction.dualTensorReduction_tmul, Algebra.smul_def, mul_one]

@[instance_reducible]
def dualScalarAlgebra : Algebra (DualNumber k) A :=
  ((algebraMap k A).comp (TrivSqZeroExt.fstHom k k k).toRingHom).toAlgebra

theorem dualScalarAlgebra_map (c : DualNumber k) :
    letI := dualScalarAlgebra k A
    algebraMap (DualNumber k) A c = algebraMap k A c.fst := rfl

def dualTensorReductionBaseEquiv :
    letI := dualScalarAlgebra k A
    ((DualNumber k ⊗[k] A) ⧸ TensorReduction.dualTensorReductionIdeal k A) ≃ₐ[DualNumber k] A := by
  let := dualScalarAlgebra k A
  refine { (dualTensorReductionQuotientEquiv k A).toRingEquiv with commutes' := ?_ }
  intro c
  change dualTensorReductionQuotientEquiv k A
    (Ideal.Quotient.mk (TensorReduction.dualTensorReductionIdeal k A)
      (algebraMap (DualNumber k) (DualNumber k ⊗[k] A) c)) = algebraMap k A c.fst
  rw [dualTensorReductionQuotientEquiv_mk]
  exact dualTensorReduction_algebraMap k A c

theorem dualTensorReductionBaseEquiv_mk (u : DualNumber k ⊗[k] A) :
    dualTensorReductionBaseEquiv k A
      (Ideal.Quotient.mk (TensorReduction.dualTensorReductionIdeal k A) u) = TensorReduction.dualTensorReduction k A u :=
  dualTensorReductionQuotientEquiv_mk k A u

def dualTensorCanonicalReductionEquiv :
    letI := dualScalarAlgebra k A
    ((DualNumber k ⊗[k] A) ⧸ (TensorReduction.dualScalarReductionIdeal k).map
      (algebraMap (DualNumber k) (DualNumber k ⊗[k] A))) ≃ₐ[DualNumber k] A := by
  let := dualScalarAlgebra k A
  exact (Ideal.quotientEquivAlgOfEq (DualNumber k) (dualTensorReductionIdeal_eq_map k A).symm).trans
    (dualTensorReductionBaseEquiv k A)

theorem dualTensorCanonicalReductionEquiv_mk (u : DualNumber k ⊗[k] A) :
    dualTensorCanonicalReductionEquiv k A
      (Ideal.Quotient.mk ((TensorReduction.dualScalarReductionIdeal k).map
        (algebraMap (DualNumber k) (DualNumber k ⊗[k] A))) u) = TensorReduction.dualTensorReduction k A u := by
  change dualTensorReductionBaseEquiv k A
    (Ideal.quotientEquivAlgOfEq (DualNumber k) (dualTensorReductionIdeal_eq_map k A).symm
      (Ideal.Quotient.mk _ u)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk]
  exact dualTensorReductionBaseEquiv_mk k A u

end

/-! The canonical constant-product reduction respects any given
dual-number base action whose literal map is coefficient reduction. -/

open scoped TensorProduct

variable (k B : Type) [CommRing k] [CommRing B] [Algebra k B] [Algebra (DualNumber k) B]
    (hB : ∀ c : DualNumber k, algebraMap (DualNumber k) B c = algebraMap k B c.fst)

local instance dualReductionWithBase_ring : CommRing (DualNumber k ⊗[k] B) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := B)

def dualTensorReductionWithBase :
    ((DualNumber k ⊗[k] B) ⧸ (TensorReduction.dualScalarReductionIdeal k).map
      (algebraMap (DualNumber k) (DualNumber k ⊗[k] B))) ≃ₐ[DualNumber k] B where
  __ := (dualTensorReductionQuotientEquiv k B).toRingEquiv
  commutes' c := by
    change dualTensorReductionQuotientEquiv k B
      (Ideal.Quotient.mk (TensorReduction.dualTensorReductionIdeal k B)
        (algebraMap (DualNumber k) (DualNumber k ⊗[k] B) c)) = algebraMap (DualNumber k) B c
    rw [dualTensorReductionQuotientEquiv_mk, dualTensorReduction_algebraMap, hB]

theorem dualTensorReductionWithBase_mk (p : DualNumber k ⊗[k] B) :
    dualTensorReductionWithBase k B hB (Ideal.Quotient.mk ((TensorReduction.dualScalarReductionIdeal k).map
      (algebraMap (DualNumber k) (DualNumber k ⊗[k] B))) p) = TensorReduction.dualTensorReduction k B p :=
  dualTensorReductionQuotientEquiv_mk k B p

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorReductionEquiv
