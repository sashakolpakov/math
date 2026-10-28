import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainCRTCore
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterInput

namespace OAI.Algorithms

/-! The actual CRT preparation produces the literal entry state of the
outer CRT controller. Every premise below identifies an existing word;
the clearing, context copies, and unary conversion are already executed
by the checked preparation program. -/

namespace SubexponentialSAT.SubexpMainCRTInput

open BitProgram StructuredCalls SubexpMainProgram SubexpMainCRT
open SubexpLiftRing SubexpQuarticRing SubexpPolynomialPowerProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

def entryWords (modulus width reduction exponent one minusOne : List Bool)
    (D : ℕ) (nodes jets : List Bool) (i : Fin 320) : List Bool :=
  if i.val = 5 then modulus else if i.val = 10 then width else
  if i.val = 194 then modulus else if i.val = 201 then reduction else
  if i.val = 202 then width else if i.val = 206 then exponent else
  if i.val = 207 then one else if i.val = 211 then minusOne else
  if i.val = 243 then List.replicate D true else
  if i.val = 256 then nodes else if i.val = 265 then jets else []

theorem preparation_word (a : SubexpCRTPreparation.Data) (i : Fin 320) :
    (SubexpCRTPreparation.result a).stacks (i.castAdd 10) =
      entryWords (a.stacks 320) (a.stacks 321) (a.stacks 322) (a.stacks 323)
        (a.stacks 324) (a.stacks 325) (CounterPrograms.value (a.stacks 326))
        (a.stacks 256) (a.stacks 265) i := by
  by_cases h5 : i.val = 5
  · have hi : i = 5 := Fin.ext h5
    subst i
    exact SubexpCRTPreparation.result_word a (320, 5) (by simp [SubexpCRTPreparation.copies]) (by decide)
  by_cases h10 : i.val = 10
  · have hi : i = 10 := Fin.ext h10
    subst i
    exact SubexpCRTPreparation.result_word a (321, 10) (by simp [SubexpCRTPreparation.copies]) (by decide)
  by_cases h194 : i.val = 194
  · have hi : i = 194 := Fin.ext h194
    subst i
    exact SubexpCRTPreparation.result_word a (320, 194) (by simp [SubexpCRTPreparation.copies]) (by decide)
  by_cases h201 : i.val = 201
  · have hi : i = 201 := Fin.ext h201
    subst i
    exact SubexpCRTPreparation.result_word a (322, 201) (by simp [SubexpCRTPreparation.copies]) (by decide)
  by_cases h202 : i.val = 202
  · have hi : i = 202 := Fin.ext h202
    subst i
    exact SubexpCRTPreparation.result_word a (321, 202) (by simp [SubexpCRTPreparation.copies]) (by decide)
  by_cases h206 : i.val = 206
  · have hi : i = 206 := Fin.ext h206
    subst i
    exact SubexpCRTPreparation.result_word a (323, 206) (by simp [SubexpCRTPreparation.copies]) (by decide)
  by_cases h207 : i.val = 207
  · have hi : i = 207 := Fin.ext h207
    subst i
    exact SubexpCRTPreparation.result_word a (324, 207) (by simp [SubexpCRTPreparation.copies]) (by decide)
  by_cases h211 : i.val = 211
  · have hi : i = 211 := Fin.ext h211
    subst i
    exact SubexpCRTPreparation.result_word a (325, 211) (by simp [SubexpCRTPreparation.copies]) (by decide)
  by_cases h243 : i.val = 243
  · have hi : i = 243 := Fin.ext h243
    subst i
    exact SubexpCRTPreparation.result_unary a
  by_cases h256 : i.val = 256
  · have hi : i = 256 := Fin.ext h256
    subst i
    exact SubexpCRTPreparation.result_nodes a
  by_cases h265 : i.val = 265
  · have hi : i = 265 := Fin.ext h265
    subst i
    exact SubexpCRTPreparation.result_jets a
  have hclear : SubexpCRTPreparation.NeedsClear (i.castAdd 10) := by
    apply Or.inl
    refine ⟨i.isLt, ?_, ?_⟩
    · intro he
      exact h256 (congrArg (fun j : Fin 330 => j.val) he)
    · intro he
      exact h265 (congrArg (fun j : Fin 330 => j.val) he)
  have hd : ∀ q ∈ SubexpCRTPreparation.copies, i.castAdd 10 ≠ q.2 := by
    intro q hq
    simp only [SubexpCRTPreparation.copies, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals intro he
    all_goals have hv := congrArg (fun j : Fin 330 => j.val) he
    all_goals norm_num only [Fin.val_castAdd, Fin.coe_ofNat_eq_mod] at hv
    all_goals omega
  have he := SubexpCRTPreparation.result_empty a (i.castAdd 10) hclear hd
    (by intro he; exact h243 (congrArg (fun j : Fin 330 => j.val) he))
  simpa only [entryWords, ite_eq_right h5, ite_eq_right h10, ite_eq_right h194, ite_eq_right h201,
    ite_eq_right h202, ite_eq_right h206, ite_eq_right h207, ite_eq_right h211, ite_eq_right h243,
    ite_eq_right h256, ite_eq_right h265] using he

theorem outer_store (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (t one : Coefficient p (D + 1)) (minusOne : Word (baseWidth p (D + 1)))
    (width exponent : List Bool) {Q : ℕ}
    (nodes : Fin Q → Coefficient p (D + 1)) (jets : Fin Q → FixedPolynomial p (D + 1) D)
    (i : Fin 320) :
    SubexpCRTOuterInput.store p D M t one minusOne width exponent nodes jets i =
      entryWords M.bits width (SubexpFlatAdd.encode t) exponent (SubexpFlatAdd.encode one)
        minusOne.val D ((List.finRange Q).flatMap (fun j => SubexpFlatAdd.encode (nodes j)))
        ((List.finRange Q).flatMap (fun j => encode p (D + 1) (jets j))) i := by
  fin_cases i <;> rfl

/-- Literal word identities suffice because the preparation establishes every
empty scratch location and resets every register itself. -/
theorem prepared_eq_outerInput {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (p D : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p (D + 1))
    (t one : Coefficient p (D + 1)) (minusOne : Word (baseWidth p (D + 1)))
    (width exponent : List Bool) {Q : ℕ}
    (nodes : Fin Q → Coefficient p (D + 1)) (jets : Fin Q → FixedPolynomial p (D + 1) D)
    (hM : a.stacks (persistent es 12) = M.bits)
    (hwidth : a.stacks (persistent es 13) = width)
    (ht : a.stacks (persistent es 14) = SubexpFlatAdd.encode t)
    (hexp : a.stacks (persistent es 29) = exponent)
    (hone : a.stacks (persistent es 30) = SubexpFlatAdd.encode one)
    (hminus : a.stacks (persistent es 31) = minusOne.val)
    (hD : CounterPrograms.value (a.stacks (persistent es 19)) = D)
    (hnodes : a.stacks (ordinary alloc 256) =
      (List.finRange Q).flatMap (fun j => SubexpFlatAdd.encode (nodes j)))
    (hjets : a.stacks (ordinary alloc 265) =
      (List.finRange Q).flatMap (fun j => encode p (D + 1) (jets j))) :
    projectCRT alloc (preparedData alloc a) =
      SubexpCRTOuterInput.data p D M t one minusOne width exponent nodes jets (fun _ => false) := by
  rw [prepared_entry]
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  let localStart : SubexpCRTPreparation.Data := (preparation er alloc).project a
  change (SubexpCRTPreparation.result localStart).stacks (i.castAdd 10) =
    SubexpCRTOuterInput.store p D M t one minusOne width exponent nodes jets i
  rw [preparation_word, outer_store]
  have hi (j : Fin 7) : localStart.stacks (SubexpCRTPreparation.inputPort j) =
      a.stacks (persistent es (inputIndex j)) := by
    change a.stacks (stackMap alloc (SubexpCRTPreparation.inputPort j)) = _
    rw [stackMap_input]
  have hn : localStart.stacks 256 = a.stacks (ordinary alloc 256) := rfl
  have hj : localStart.stacks 265 = a.stacks (ordinary alloc 265) := rfl
  rw [show localStart.stacks 320 = M.bits from (hi 0).trans hM,
    show localStart.stacks 321 = width from (hi 1).trans hwidth,
    show localStart.stacks 322 = SubexpFlatAdd.encode t from (hi 2).trans ht,
    show localStart.stacks 323 = exponent from (hi 3).trans hexp,
    show localStart.stacks 324 = SubexpFlatAdd.encode one from (hi 4).trans hone,
    show localStart.stacks 325 = minusOne.val from (hi 5).trans hminus,
    show localStart.stacks 326 = a.stacks (persistent es 19) from hi 6,
    hD, hn, hj, hnodes, hjets]

end SubexponentialSAT.SubexpMainCRTInput

end OAI.Algorithms
