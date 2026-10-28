import OAI.AlgebraicGeometry.CycleClass.Thom.SurjectiveModuleSupport
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.LocalRing.Quotient

/-! # Equation Quotient Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Regular.EquationQuotientSupport.Constructions

noncomputable section

/-! Passing to the quotient by the first regular equation preserves
the actual residual ideal, local maximal-ideal condition, module support
isolation, and support dimension used in the next induction step. -/

open RingTheory.Sequence
open scoped Pointwise

set_option backward.isDefEq.respectTransparency false

universe u v
variable (R : Type u) [CommRing R] [IsLocalRing R] (r : R)
  (hrm : r ∈ IsLocalRing.maximalIdeal R)

include hrm in
theorem quotientLocalRing : IsLocalRing (R ⧸ Ideal.span {r}) := by
  have hi : Ideal.span {r} ≠ (⊤ : Ideal R) := ne_top_of_le_ne_top
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hrm))
  let : Nontrivial (R ⧸ Ideal.span {r}) := Ideal.Quotient.nontrivial_iff.mpr hi
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {r})) Ideal.Quotient.mk_surjective

variable [IsLocalRing (R ⧸ Ideal.span {r})]
local instance : IsLocalHom (algebraMap R (R ⧸ Ideal.span {r})) :=
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

omit [IsLocalRing R] [IsLocalRing (R ⧸ Ideal.span {r})] in
theorem ideal_map_head (rs : List R) :
    (Ideal.ofList (r :: rs)).map (algebraMap R (R ⧸ Ideal.span {r})) =
      Ideal.ofList (rs.map (algebraMap R (R ⧸ Ideal.span {r}))) := by
  have hz : algebraMap R (R ⧸ Ideal.span {r}) r = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  rw [Ideal.map_ofList, List.map_cons, hz, Ideal.ofList_cons, Ideal.span_singleton_zero, bot_sup_eq]

theorem maximalIdeal_tail (rs : List R) (hm : ∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal R) :
    ∀ x ∈ rs.map (algebraMap R (R ⧸ Ideal.span {r})), x ∈ IsLocalRing.maximalIdeal (R ⧸ Ideal.span {r}) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact map_nonunit (algebraMap R (R ⧸ Ideal.span {r})) y (hm y hy)

variable (N : Type v) [AddCommGroup N] [Module R N] [Module.Finite R N]

theorem isolated_tail (rs : List R)
    (hi : PrimeSpectrum.zeroLocus (Ideal.ofList (r :: rs) : Set R) ∩ Module.support R N ⊆
      {IsLocalRing.closedPoint R}) :
    PrimeSpectrum.zeroLocus (Ideal.ofList (rs.map (algebraMap R (R ⧸ Ideal.span {r}))) :
      Set (R ⧸ Ideal.span {r})) ∩ Module.support (R ⧸ Ideal.span {r}) (QuotSMulTop r N) ⊆
      {IsLocalRing.closedPoint (R ⧸ Ideal.span {r})} := by
  have hs : Module.support R (QuotSMulTop r N) ⊆ Module.support R N :=
    Module.support_subset_of_surjective (r • (⊤ : Submodule R N)).mkQ (Submodule.mkQ_surjective _)
  have h := SurjectiveModuleSupport.Constructions.isolated_ideal_intersection R (R ⧸ Ideal.span {r})
    (QuotSMulTop r N) Ideal.Quotient.mk_surjective (Ideal.ofList (r :: rs))
    ((Set.inter_subset_inter_right _ hs).trans hi)
  rw [ideal_map_head R r rs] at h
  exact h

omit [IsLocalRing R] [IsLocalRing (R ⧸ Ideal.span {r})] in
theorem quotient_supportDim :
    Module.supportDim (R ⧸ Ideal.span {r}) (QuotSMulTop r N) = Module.supportDim R (QuotSMulTop r N) :=
  (SurjectiveModuleDimension.Constructions.supportDim_eq R (R ⧸ Ideal.span {r}) (QuotSMulTop r N)
    Ideal.Quotient.mk_surjective).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Regular.EquationQuotientSupport.Constructions
