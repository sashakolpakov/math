import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamilyEnumeration

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashFamily

open scoped BigOperators
open Finset

/-- A combined alphabet digit is `coordinate + m * coefficient`. -/
def digitEquiv (m : ℕ) : (Fin m × ZMod 3) ≃ Fin (3 * m) :=
  (Equiv.prodCongr (Equiv.refl (Fin m)) (ZMod.finEquiv 3).symm.toEquiv).trans
    ((Equiv.prodComm (Fin m) (Fin 3)).trans finProdFinEquiv)

theorem digitEquiv_val (m : ℕ) (i : Fin m) (c : ZMod 3) :
    (digitEquiv m (i, c)).val = i.val + m * c.val := rfl

/-- Coordinate/coefficient tuples are equivalent to strings in the combined
alphabet, keeping every occurrence separately even when coordinates repeat. -/
def candidateDigitsEquiv (m d : ℕ) : Candidate m d ≃ (Fin d → Fin (3 * m)) :=
  (Equiv.arrowProdEquivProdArrow (Fin d) (fun _ => Fin m) (fun _ => ZMod 3)).symm.trans
    (Equiv.piCongrRight fun _ => digitEquiv m)

def decodeDigits {m d : ℕ} (a : Fin d → Fin (3 * m)) : Candidate m d :=
  (candidateDigitsEquiv m d).symm a

theorem decodeDigits_bijective (m d : ℕ) :
    Function.Bijective (@decodeDigits m d) :=
  (candidateDigitsEquiv m d).symm.bijective

theorem decodeDigits_coordinate {m d : ℕ} (a : Fin d → Fin (3 * m)) (j : Fin d) :
    (decodeDigits a).1 j = ((digitEquiv m).symm (a j)).1 := rfl

theorem decodeDigits_coefficient {m d : ℕ} (a : Fin d → Fin (3 * m)) (j : Fin d) :
    (decodeDigits a).2 j = ((digitEquiv m).symm (a j)).2 := rfl

def candidateDigitIndexEquiv (m d : ℕ) : Candidate m d ≃ Fin ((3 * m) ^ d) :=
  (candidateDigitsEquiv m d).trans finFunctionFinEquiv

/-- Runtime-friendly base-`3*m` enumeration; position zero is least significant. -/
def enumerateDigits (m d : ℕ) : Fin ((3 * m) ^ d) → Candidate m d :=
  (candidateDigitIndexEquiv m d).symm

theorem candidateDigitIndexEquiv_val {m d : ℕ} (h : Candidate m d) :
    (candidateDigitIndexEquiv m d h).val =
      ∑ j : Fin d, ((h.1 j).val + m * (h.2 j).val) * (3 * m) ^ j.val := by
  rfl

theorem enumerateDigits_bijective (m d : ℕ) :
    Function.Bijective (enumerateDigits m d) :=
  (candidateDigitIndexEquiv m d).symm.bijective

/-- Any bijective listing is valid, including a program's different tuple
order. This theorem imposes no choice operation on the supplied listing. -/
theorem listing_detection {ι : Type*} [Fintype ι] [DecidableEq ι] {m d : ℕ}
    (family : ι → Candidate m d) (hf : Function.Bijective family)
    (v : Fin m → ZMod 3) (hm : 0 < m) (heavy : m ≤ d * supportCard v) :
    Fintype.card ι ≤ 3 * (univ.filter fun a : ι =>
      (∑ j, row (family a) j * v j) ≠ 0).card := by
  classical
  let e := Equiv.ofBijective family hf
  have hc : (univ.filter fun a : ι => eval (family a) v ≠ 0).card =
      detectingCard (d := d) v := by
    unfold detectingCard
    exact Finset.card_equiv e (fun a => by
      constructor
      · intro ha
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simpa only [e, Equiv.ofBijective_apply] using (Finset.mem_filter.mp ha).2
      · intro ha
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simpa only [e, Equiv.ofBijective_apply] using (Finset.mem_filter.mp ha).2)
  simp_rw [row_dot]
  rw [hc, Fintype.card_congr e]
  exact detecting_card_lower v hm heavy

theorem enumerateDigits_detection {m d : ℕ} (v : Fin m → ZMod 3) (hm : 0 < m)
    (heavy : m ≤ d * supportCard v) :
    (3 * m) ^ d ≤
      3 * (univ.filter fun i : Fin ((3 * m) ^ d) =>
        (∑ j, row (enumerateDigits m d i) j * v j) ≠ 0).card := by
  classical
  have hc :
      (univ.filter fun i : Fin ((3 * m) ^ d) =>
        eval (enumerateDigits m d i) v ≠ 0).card = detectingCard (d := d) v := by
    unfold detectingCard
    exact Finset.card_equiv (candidateDigitIndexEquiv m d).symm (fun i => by
      constructor
      · intro hi
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simpa only [enumerateDigits] using (Finset.mem_filter.mp hi).2
      · intro hi
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simpa only [enumerateDigits] using (Finset.mem_filter.mp hi).2)
  simp_rw [row_dot]
  rw [hc, ← candidate_card]
  exact detecting_card_lower v hm heavy

end SubexponentialSAT.SqrtLog.HashFamily

end OAI.Algorithms
