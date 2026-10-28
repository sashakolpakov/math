import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RegularSequence
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Concatenated Regularity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ConcatenatedRegularity

noncomputable section

/-! Regular normal equations followed by regular quotient parameters
form a regular ambient Koszul sequence, over any commutative base. -/
open RingTheory.Sequence
universe u v
variable {A : Type u} [CommRing A]

theorem append_list (I : Ideal A) (s t : List A) (hI : Ideal.ofList s = I)
    (hs : IsWeaklyRegular A s)
    (ht : IsWeaklyRegular (A ⧸ I) (t.map (Ideal.Quotient.mk I))) :
    IsWeaklyRegular A (s ++ t) := by
  apply (isWeaklyRegular_append_iff A s t).mpr
  refine ⟨hs, ?_⟩
  have he : (Ideal.ofList s • (⊤ : Ideal A)) = I := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, hI]
  let e := Submodule.quotEquivOfEq _ _ he
  apply (e.isWeaklyRegular_congr t).mpr
  exact (isWeaklyRegular_map_algebraMap_iff (A ⧸ I) (A ⧸ I) t).mp ht

theorem append (I : Ideal A) {c m : ℕ} (s : Fin c → A) (t : Fin m → A)
    (hI : Ideal.span (Set.range s) = I)
    (hs : IsWeaklyRegular A (List.ofFn s))
    (ht : IsWeaklyRegular (A ⧸ I) (List.ofFn (fun i => Ideal.Quotient.mk I (t i)))) :
    IsWeaklyRegular A (List.ofFn (Fin.append s t)) := by
  rw [List.ofFn_fin_append]
  apply append_list I _ _ (by rw [Smooth.RegularSequence.CoordinateRegularity.ofList_ofFn]; exact hI) hs
  simpa only [List.map_ofFn, Function.comp_def] using ht

theorem quotient_parameters {B : Type v} [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) {m : ℕ} (t : Fin m → A)
    (ht : IsWeaklyRegular B (List.ofFn (fun i => f (t i)))) :
    IsWeaklyRegular (A ⧸ RingHom.ker f)
      (List.ofFn (fun i => Ideal.Quotient.mk (RingHom.ker f) (t i))) := by
  let e := f.quotientKerEquivOfSurjective hf
  have he : IsWeaklyRegular (A ⧸ RingHom.ker f)
      (List.ofFn (fun i => Ideal.Quotient.mk (RingHom.ker f) (t i))) ↔
      IsWeaklyRegular B
        ((List.ofFn (fun i => Ideal.Quotient.mk (RingHom.ker f) (t i))).map e) :=
    e.toAddEquiv.isWeaklyRegular_congr (List.forall₂_map_right_iff.mpr
      (List.forall₂_same.mpr (fun r _ x => e.map_mul r x)))
  apply he.mpr
  simpa only [List.map_ofFn, Function.comp_def, e,
    RingHom.quotientKerEquivOfSurjective_apply_mk] using ht

theorem append_of_surjective {B : Type v} [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) {c m : ℕ} (s : Fin c → A) (t : Fin m → A)
    (hI : Ideal.span (Set.range s) = RingHom.ker f)
    (hs : IsWeaklyRegular A (List.ofFn s))
    (ht : IsWeaklyRegular B (List.ofFn (fun i => f (t i)))) :
    IsWeaklyRegular A (List.ofFn (Fin.append s t)) :=
  ConcatenatedRegularity.append (RingHom.ker f) s t hI hs (quotient_parameters f hf t ht)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Koszul.ConcatenatedRegularity
