import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Equation Quotients -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Regular.EquationQuotients.Constructions

noncomputable section

/-! The actual quotient by one equation and the quotient by the
remaining equations agree with the quotient by the entire sequence.
Regularity passes to the residual sequence over the quotient ring. -/

open RingTheory.Sequence
open scoped Pointwise

set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R] (r : R)

theorem smul_top_eq_span :
    (r • (⊤ : Submodule R R) : Ideal R) = Ideal.span {r} := by
  rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]

def headQuotientEquiv : QuotSMulTop r R ≃ₗ[R ⧸ Ideal.span {r}] R ⧸ Ideal.span {r} :=
  (Submodule.quotEquivOfEq _ _ (smul_top_eq_span R r)).extendScalarsOfSurjective
    (show Function.Surjective (algebraMap R (R ⧸ Ideal.span {r})) from Ideal.Quotient.mk_surjective)

theorem weaklyRegular_tail (rs : List R) (hr : IsWeaklyRegular R (r :: rs)) :
    IsWeaklyRegular (R ⧸ Ideal.span {r})
      (rs.map (algebraMap R (R ⧸ Ideal.span {r}))) :=
  ((headQuotientEquiv R r).isWeaklyRegular_congr _).mp
    ((isWeaklyRegular_cons_iff' R r rs).mp hr).2

def sequenceQuotientEquiv (rs : List R) :
    ((R ⧸ Ideal.span {r}) ⧸ Ideal.ofList (rs.map (algebraMap R (R ⧸ Ideal.span {r})))) ≃ₐ[R]
      R ⧸ Ideal.ofList (r :: rs) :=
  ((Ideal.quotientEquivAlgOfEq R (Ideal.map_ofList _ rs).symm).trans
    (DoubleQuot.quotQuotEquivQuotSupₐ R (Ideal.span {r}) (Ideal.ofList rs))).trans
      (Ideal.quotientEquivAlgOfEq R (Ideal.ofList_cons r rs).symm)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Regular.EquationQuotients.Constructions
