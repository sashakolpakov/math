import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpArgumentCode

namespace OAI.Algorithms

/-! Coordinate-major raw incidence arguments, matching physical Taylor caches. -/
namespace SubexponentialSAT.SubexpColumnArgumentCode

open SubexpArgumentCode
open scoped BigOperators

/-- One coordinate's Taylor coefficients, beginning with its marked U term. -/
def columnTerms {D q : ℕ} {A : Type*} (i : Fin D) (a : Fin (q+1) → A) : SymbolicCost.CoeffList D A :=
  List.ofFn (fun j => (coordinateIndex i (if j.val=0 then 1 else 0) j.val,a j))

/-- The supplied negative value is explicit here; the machine producer computes
it with the coefficient-ring negation program before invoking this serializer. -/
def compileColumns {D q : ℕ} {A : Type*} (beta negative : A) (a : Fin (q+1) → Fin D → A) :
    SymbolicCost.CoeffList D A :=
  [(constantIndex D 0 0,beta),(constantIndex D 1 0,negative)] ++
    (List.ofFn (fun i : Fin D => columnTerms i (fun j => a j i))).flatten

@[simp] theorem columnTerms_length {D q : ℕ} {A : Type*} (i : Fin D) (a : Fin (q+1) → A) :
    (columnTerms i a).length = q+1 := by simp [columnTerms]

@[simp] theorem compileColumns_length {D q : ℕ} {A : Type*} (beta negative : A)
    (a : Fin (q+1) → Fin D → A) : (compileColumns beta negative a).length = 2+(q+1)*D := by
  simp [compileColumns,List.length_flatten,List.map_ofFn,Fin.sum_ofFn,Nat.mul_comm]
  omega

theorem map_compileColumns {D q : ℕ} {A B : Type*} (decode : A → B) (beta negative : A)
    (a : Fin (q+1) → Fin D → A) :
    (compileColumns beta negative a).map (fun t => (t.1,decode t.2)) =
      compileColumns (decode beta) (decode negative) (fun j i => decode (a j i)) := by
  simp [compileColumns,columnTerms,List.map_flatten,Function.comp_def]

noncomputable section

variable {D q : ℕ} {A : Type*} [CommRing A]

theorem denote_columnTerms (i : Fin D) (a : Fin (q+1) → A) :
    SymbolicCost.denote (columnTerms i a) =
      ∑ j : Fin (q+1), SymbolicCost.monomial (coordinateIndex i (if j.val=0 then 1 else 0) j.val) (a j) := by
  rw [denote_eq_sum]
  simp only [columnTerms,List.map_ofFn,Fin.sum_ofFn,Function.comp_apply]

theorem denote_compileColumns (beta negative : A) (a : Fin (q+1) → Fin D → A) :
    SymbolicCost.denote (compileColumns beta negative a) =
      SymbolicCost.monomial (constantIndex D 0 0) beta +
      SymbolicCost.monomial (constantIndex D 1 0) negative +
      ∑ i : Fin D, ∑ j : Fin (q+1),
        SymbolicCost.monomial (coordinateIndex i (if j.val=0 then 1 else 0) j.val) (a j i) := by
  simp [compileColumns,denote_flatten,
    SymbolicCost.denote,denote_columnTerms,List.map_ofFn,Fin.sum_ofFn,add_assoc]

theorem denote_compileColumns_eq (beta : A) (a : Fin (q+1) → Fin D → A) :
    SymbolicCost.denote (compileColumns beta (-beta) a) = SymbolicCost.denote (compileArgument beta a) := by
  rw [denote_compileColumns,Finset.sum_comm]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,↓reduceIte,Fin.val_succ,Nat.add_eq_zero_iff,one_ne_zero,and_false]
  simp [compileArgument,denote_eq_sum,rawRow,
    List.map_ofFn,Fin.sum_ofFn,add_assoc]

/-- Coefficient decoding supplies the ring structure. Raw word coefficients
need no artificial ring instance, and the negation equality is the sole local
arithmetic interface. -/
theorem decoded_denote_eq {C : Type*} (decode : C → A) (beta negative : C)
    (a : Fin (q+1) → Fin D → C) (hnegative : decode negative = -(decode beta)) :
    SymbolicCost.denote ((compileColumns beta negative a).map (fun t => (t.1,decode t.2))) =
      SymbolicCost.denote (compileArgument (decode beta) (fun j i => decode (a j i))) := by
  rw [map_compileColumns,hnegative,denote_compileColumns_eq]

end
end SubexponentialSAT.SubexpColumnArgumentCode

end OAI.Algorithms
