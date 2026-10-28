import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.SequenceBasic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # Parameter Quotient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.ParameterQuotient

noncomputable section

/-! Quotienting a local ring by the first regular parameter carries the remaining regular sequence to generators of the quotient maximal ideal. -/
open IsLocalRing
universe u

theorem regular_parameters_quotient
    {R : Type u} [CommRing R] [IsLocalRing R] (r : R) (rs : List R)
    [IsLocalRing (R ⧸ Ideal.span {r})]
    (hreg : SequenceBasic.RingTheory.Sequence.IsRegular R (r :: rs)) (hgen : SequenceBasic.Ideal.ofList (r :: rs) = maximalIdeal R) :
    SequenceBasic.RingTheory.Sequence.IsRegular (R ⧸ Ideal.span {r}) (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) ∧
      SequenceBasic.Ideal.ofList (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) =
        maximalIdeal (R ⧸ Ideal.span {r}) := by
  let S := R ⧸ Ideal.span {r}
  let e : QuotSMulTop r R ≃ₗ[R] S :=
    (QuotSMulTop.equivQuotTensor r R).trans (TensorProduct.rid R S)
  let eS : QuotSMulTop r R ≃ₗ[S] S :=
    e.extendScalarsOfSurjective (show Function.Surjective (algebraMap R S) from Ideal.Quotient.mk_surjective)
  have htail : SequenceBasic.RingTheory.Sequence.IsRegular (QuotSMulTop r R) (rs.map (Ideal.Quotient.mk (Ideal.span {r}))) :=
    ((SequenceBasic.RingTheory.Sequence.isRegular_cons_iff' R r rs).mp hreg).2
  refine ⟨(SequenceBasic.LinearEquiv.isRegular_congr eS _).mp htail, ?_⟩
  have hmkr : Ideal.Quotient.mk (Ideal.span {r}) r = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton r))
  have hmap := congrArg (Ideal.map (Ideal.Quotient.mk (Ideal.span {r}))) hgen
  rw [SequenceBasic.Ideal.map_ofList, List.map_cons, hmkr, SequenceBasic.Ideal.ofList_cons] at hmap
  simpa using hmap.trans (IsLocalRing.map_maximalIdeal_of_surjective
    (Ideal.Quotient.mk (Ideal.span {r})) Ideal.Quotient.mk_surjective)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.ParameterQuotient
