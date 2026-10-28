import OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.CoordinateRegularity
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Data.List.OfFn

/-! # Regular Sequence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RegularSequence.CoordinateRegularity

noncomputable section

/-! Regular sequences supplied by dual coordinates over an arbitrary base. -/

universe u

theorem ofList_ofFn (A : Type*) [CommRing A] {r : ℕ} (z : Fin r → A) :
    Ideal.ofList (List.ofFn z) = Ideal.span (Set.range z) := by
  unfold Ideal.ofList
  congr 1
  ext a
  exact List.mem_ofFn' z a

theorem ofList_take_ofFn (A : Type*) [CommRing A] {r : ℕ} (z : Fin r → A)
    (j : Fin r) :
    Ideal.ofList ((List.ofFn z).take j) =
      Ideal.span (z '' {i : Fin r | i < j}) := by
  unfold Ideal.ofList
  congr 1
  ext a
  simp only [Set.mem_ofPred_eq, List.mem_take_iff_getElem, List.length_ofFn,
    List.getElem_ofFn, Set.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, (Nat.lt_min.mp hi).2⟩, (Nat.lt_min.mp hi).1, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.val, Nat.lt_min.mpr ⟨hi, i.isLt⟩, rfl⟩

theorem family_isWeaklyRegular {k A : Type u}
    [CommRing k] [CommRing A] [Algebra k A] [Algebra.Smooth k A] {r : ℕ}
    (z : Fin r → A) (D : Fin r → Derivation k A A)
    (hD : ∀ i j, D i (z j) = if i = j then 1 else 0) :
    RingTheory.Sequence.IsWeaklyRegular A (List.ofFn z) := by
  refine ⟨fun i hi => ?_⟩
  have hir : i < r := by simpa only [List.length_ofFn] using hi
  have h := CoordinateRegularity.family_coordinate_regular_mod_preceding z D hD ⟨i, hir⟩
  rw [← ofList_take_ofFn A z ⟨i, hir⟩] at h
  rw [Ideal.smul_eq_mul, Ideal.mul_top]
  simp only [List.getElem_ofFn]
  intro x y hxy
  apply h.left
  simpa only [← Ideal.Quotient.algebraMap_eq, Algebra.smul_def] using hxy

theorem family_isRegular {k A : Type u}
    [CommRing k] [CommRing A] [Algebra k A] [Algebra.Smooth k A] {r : ℕ}
    (z : Fin r → A) (D : Fin r → Derivation k A A)
    (hD : ∀ i j, D i (z j) = if i = j then 1 else 0)
    (hproper : Ideal.span (Set.range z) ≠ ⊤) :
    RingTheory.Sequence.IsRegular A (List.ofFn z) := by
  refine ⟨family_isWeaklyRegular z D hD, ?_⟩
  rw [Ideal.smul_eq_mul, Ideal.mul_top, ofList_ofFn]
  exact hproper.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Smooth.RegularSequence.CoordinateRegularity
