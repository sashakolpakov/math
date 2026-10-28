import Mathlib.RingTheory.Regular.RegularSequence

/-! # Sequence Tail Change -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Regular.SequenceTailChange.Constructions

noncomputable section

/-! Adding a combination of the remaining equations to the first
equation preserves the generated ideal and regularity over a local ring. -/

open RingTheory.Sequence
open scoped Pointwise

universe u v
variable {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

theorem quotient_smul_eq_zero (I : Ideal R) (t : R) (ht : t ∈ I)
    (y : M ⧸ (I • ⊤ : Submodule R M)) : t • y = 0 := by
  obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (I • ⊤ : Submodule R M) y
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul ht (Submodule.mem_top : m ∈ (⊤ : Submodule R M))

theorem regular_add_annihilator (x t : R) (ht : ∀ y : M, t • y = 0) (hx : IsSMulRegular M x) :
    IsSMulRegular M (x + t) := by
  change Function.Injective (fun y : M => (x + t) • y)
  change Function.Injective (fun y : M => x • y) at hx
  simpa only [add_smul, ht, add_zero] using hx

theorem ofList_add_tail (x t : R) (rs : List R) (ht : t ∈ Ideal.ofList rs) :
    Ideal.ofList ((x + t) :: rs) = Ideal.ofList (x :: rs) := by
  have htail : Ideal.ofList rs ≤ Ideal.ofList (x :: rs) :=
    Ideal.span_mono (fun _ h => List.mem_cons_of_mem x h)
  have htail' : Ideal.ofList rs ≤ Ideal.ofList ((x + t) :: rs) :=
    Ideal.span_mono (fun _ h => List.mem_cons_of_mem (x + t) h)
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro a ha
    rcases List.mem_cons.mp ha with he | ha
    · rw [he]
      exact (Ideal.ofList (x :: rs)).add_mem (Ideal.subset_span List.mem_cons_self) (htail ht)
    · exact Ideal.subset_span (List.mem_cons_of_mem x ha)
  · apply Ideal.span_le.mpr
    intro a ha
    rcases List.mem_cons.mp ha with he | ha
    · rw [he]
      have h := (Ideal.ofList ((x + t) :: rs)).sub_mem
        (Ideal.subset_span List.mem_cons_self) (htail' ht)
      rw [add_sub_cancel_right] at h
      exact h
    · exact Ideal.subset_span (List.mem_cons_of_mem (x + t) ha)

variable [IsLocalRing R] [IsNoetherian R M]

theorem weaklyRegular_add_tail (x t : R) (rs : List R) (ht : t ∈ Ideal.ofList rs)
    (hm : ∀ r ∈ x :: rs, r ∈ IsLocalRing.maximalIdeal R)
    (hr : IsWeaklyRegular M (x :: rs)) : IsWeaklyRegular M ((x + t) :: rs) := by
  have hp : (x :: rs).Perm (rs ++ [x]) :=
    show ([x] ++ rs).Perm (rs ++ [x]) from List.perm_append_comm
  have h := IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hr hp hm
  obtain ⟨hrs, hx⟩ := (isWeaklyRegular_append_iff M rs [x]).mp h
  have hx' : IsWeaklyRegular (M ⧸ (Ideal.ofList rs • ⊤ : Submodule R M)) [x + t] :=
    (isWeaklyRegular_singleton_iff _ _).mpr
      (regular_add_annihilator _ x t (quotient_smul_eq_zero M (Ideal.ofList rs) t ht)
        ((isWeaklyRegular_singleton_iff _ _).mp hx))
  have hnew := (isWeaklyRegular_append_iff M rs [x + t]).mpr ⟨hrs, hx'⟩
  have htail : Ideal.ofList rs ≤ IsLocalRing.maximalIdeal R :=
    Ideal.span_le.mpr (fun _ h => hm _ (List.mem_cons_of_mem x h))
  have hm' : ∀ r ∈ rs ++ [x + t], r ∈ IsLocalRing.maximalIdeal R := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hm r (List.mem_cons_of_mem x hr)
    · obtain rfl := List.mem_singleton.mp hr
      exact (IsLocalRing.maximalIdeal R).add_mem (hm x List.mem_cons_self) (htail ht)
  exact IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hnew
    (show (rs ++ [x + t]).Perm ([x + t] ++ rs) from List.perm_append_comm) hm'

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Regular.SequenceTailChange.Constructions
