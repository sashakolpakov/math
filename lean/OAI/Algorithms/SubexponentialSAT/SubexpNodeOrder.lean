import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFieldNodes

namespace OAI.Algorithms

/-!
# Interpreting the actual generated node order

A proved permutation of the explicit encoded node table determines an exact
node equivalence in that order. Reindexing searches the concrete finite lists;
it uses neither an abstract finite-field enumeration nor a chosen layout.
-/

namespace SubexponentialSAT.SubexpNodeOrder

def permutationIndex {A : Type*} [DecidableEq A]
    (xs ys : List A) (hx : xs.Nodup) (hy : ys.Nodup) (h : xs.Perm ys) :
    Fin xs.length ≃ Fin ys.length :=
  (List.Nodup.getEquiv xs hx).trans
    ((Equiv.subtypeEquivRight (fun _x => h.mem_iff)).trans
      (List.Nodup.getEquiv ys hy).symm)

theorem get_permutationIndex {A : Type*} [DecidableEq A]
    (xs ys : List A) (hx : xs.Nodup) (hy : ys.Nodup) (h : xs.Perm ys)
    (i : Fin xs.length) :
    ys.get (permutationIndex xs ys hx hy h i) = xs.get i := by
  let e := List.Nodup.getEquiv ys hy
  change (e (e.symm _)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

open SubexpFieldNodes

variable (p : ℕ) [Fact p.Prime]

/-- Executable reindexing from an actually produced permutation of the words
to the previously verified coefficient-list order. -/
def nodeIndex (words : List (List Bool)) (h : words.Perm (encodedFieldData p)) :
    Fin (p ^ 4 - 1) ≃ Fin (p ^ 4 - 1) :=
  (finCongr (h.length_eq.trans (encodedFieldData_length p)).symm).trans
    ((permutationIndex words (encodedFieldData p)
      (h.nodup_iff.mpr (encodedFieldData_nodup p)) (encodedFieldData_nodup p) h).trans
      (finCongr (encodedFieldData_length p)))

/-- The semantic field nodes in the actual generated word order. -/
noncomputable def nodeEquiv (words : List (List Bool))
    (h : words.Perm (encodedFieldData p)) :
    Fin (p ^ 4 - 1) ≃ {z : SubexpActualRing.E p // z ≠ 0} :=
  (nodeIndex p words h).trans (SubexpFieldNodes.nodeEquiv p)

def nodeCoefficients (words : List (List Bool))
    (h : words.Perm (encodedFieldData p)) (i : Fin (p ^ 4 - 1)) : Coefficients p :=
  SubexpFieldNodes.nodeCoefficients p (nodeIndex p words h i)

theorem word_at_nodeIndex (words : List (List Bool))
    (h : words.Perm (encodedFieldData p)) (i : Fin (p ^ 4 - 1)) :
    words.get ⟨i.val, by rw [h.length_eq, encodedFieldData_length]; exact i.isLt⟩ =
      encodeCoefficients p (nodeCoefficients p words h i) := by
  rw [nodeCoefficients, ← encodedFieldData_get]
  exact (get_permutationIndex words (encodedFieldData p)
    (h.nodup_iff.mpr (encodedFieldData_nodup p)) (encodedFieldData_nodup p) h
    ⟨i.val, by rw [h.length_eq, encodedFieldData_length]; exact i.isLt⟩).symm

theorem nodeEquiv_value (words : List (List Bool))
    (h : words.Perm (encodedFieldData p)) (i : Fin (p ^ 4 - 1)) :
    (nodeEquiv p words h i).val = interpret p (nodeCoefficients p words h i) := rfl

end SubexponentialSAT.SubexpNodeOrder

end OAI.Algorithms
