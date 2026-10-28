import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NilpotentFreeLifting
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.LocalizationFreeRefinement
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Generic Freeness Nilpotent Lift -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.GenericFreenessNilpotentLift

noncomputable section

/-! A common free principal open over a nilpotent reduction lifts to a
common free principal open for flat modules over the original base. -/

open TensorProduct

universe u v w
variable {R : Type u} [CommRing R]
variable {ι : Type v} (M : ι → Type w)
variable [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Flat R (M i)]

theorem generic_freeness_lift_nilpotent_reduction (N : Ideal R) (hN : IsNilpotent N)
    (b : R ⧸ N) (hb : ¬ IsNilpotent b)
    (hf : ∀ i, Module.Free (Localization.Away b)
      (Localization.Away b ⊗[R ⧸ N] ((R ⧸ N) ⊗[R] M i))) :
    ∃ s : R, ¬ IsNilpotent s ∧ ∀ i, Module.Free (Localization.Away s)
      (Localization.Away s ⊗[R] M i) := by
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective b
  have hs' : ¬ IsNilpotent s := by
    intro h
    exact hb (hs ▸ h.map (Ideal.Quotient.mk N))
  let Q := R ⧸ N
  let C := Localization.Away s
  let J := N.map (algebraMap R C)
  let D := C ⧸ J
  let E := Localization.Away b
  have hJ : IsNilpotent J := by
    obtain ⟨n, hn⟩ := hN
    refine ⟨n, ?_⟩
    change (N.map (algebraMap R C)) ^ n = 0
    rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot]
    rfl
  have hND : N ≤ RingHom.ker (algebraMap R D) := by
    intro x hx
    change algebraMap R D x = 0
    rw [IsScalarTower.algebraMap_apply R C D]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hx)
  let q : Q →+* D := Ideal.Quotient.lift N (algebraMap R D) (fun x hx => hND hx)
  have hq (x : R) : q (algebraMap R Q x) = algebraMap R D x := rfl
  let : Algebra Q D := q.toAlgebra
  let : IsScalarTower R Q D := IsScalarTower.of_algebraMap_eq (fun x => (hq x).symm)
  have hu : IsUnit (q b) := by
    rw [← hs]
    change IsUnit (algebraMap R D s)
    rw [IsScalarTower.algebraMap_apply R C D]
    exact (IsLocalization.Away.algebraMap_isUnit s).map (algebraMap C D)
  let e : E →+* D := IsLocalization.Away.lift b hu
  have he (x : Q) : e (algebraMap Q E x) = q x := IsLocalization.Away.lift_eq b hu x
  let : Algebra E D := e.toAlgebra
  let : IsScalarTower Q E D := IsScalarTower.of_algebraMap_eq (fun x => (he x).symm)
  refine ⟨s, hs', ?_⟩
  intro i
  let : Module.Free E (E ⊗[Q] (Q ⊗[R] M i)) := hf i
  let : Module.Free D (D ⊗[Q] (Q ⊗[R] M i)) :=
    Principal.LocalizationFreeRefinement.free_baseChange_along_tower (Q ⊗[R] M i) E D
  let : Module.Free D (D ⊗[R] M i) := Module.Free.of_equiv
    (AlgebraTensorModule.cancelBaseChange R Q D D (M i))
  let : Module.Free D (D ⊗[C] (C ⊗[R] M i)) := Module.Free.of_equiv
    (AlgebraTensorModule.cancelBaseChange R C D D (M i)).symm
  exact NilpotentFreeLifting.nilpotent_free_lifting (C ⊗[R] M i) J hJ

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.GenericFreenessNilpotentLift
