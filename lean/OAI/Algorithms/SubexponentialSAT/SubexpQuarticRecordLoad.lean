import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.BankRoutines

namespace OAI.Algorithms

/-!
# Loading fixed-width candidate and divisor records

Only the finite list of destination ports occurs in the command. Word lengths
and word contents are runtime data. Each replacement clears its old word and
consumes one width-sized prefix from the source.
-/

namespace SubexponentialSAT.SubexpQuarticRecordLoad

open BitProgram StructuredCalls StackRoutines SubexpScanPrimitives

abbrev replaceWord {r s : ℕ} (width counter temporary source destination : Fin s)
    (value present : Fin r) : Cmd r s :=
  .seq (.call (clearProgram destination value present))
    (takeWord width counter temporary source destination value present)

def replaced {r s : ℕ} (d : State r s) (source destination : Fin s)
    (value present : Fin r) (word rest : List Bool) : State r s :=
  ⟨readRegs d.regs value present none,
    Function.update (Function.update d.stacks source rest) destination word⟩

theorem replaceWord_eval {r s : ℕ} (width counter temporary source destination : Fin s)
    (value present : Fin r)
    (distinct : Function.Injective
      (![width, counter, temporary, source, destination] : Fin 5 → Fin s))
    (hvp : value ≠ present) (d : State r s) (word rest : List Bool)
    (hs : d.stacks source = word ++ rest)
    (hc : d.stacks counter = []) (ht : d.stacks temporary = [])
    (hw : (d.stacks width).length = word.length) :
    Eval (replaceWord width counter temporary source destination value present)
      (2 * (d.stacks destination).length + 14 * word.length + 14) d
      (replaced d source destination value present word rest) := by
  have hwd : width ≠ destination := distinct.ne (by decide : (0 : Fin 5) ≠ 4)
  have hcd : counter ≠ destination := distinct.ne (by decide : (1 : Fin 5) ≠ 4)
  have htd : temporary ≠ destination := distinct.ne (by decide : (2 : Fin 5) ≠ 4)
  have hsd : source ≠ destination := distinct.ne (by decide : (3 : Fin 5) ≠ 4)
  let d₁ : State r s :=
    ⟨readRegs d.regs value present none, clearStacks destination d.stacks⟩
  have h₁ := BankRoutines.clear_call_eval destination value present d.regs d.stacks
  have h₂ := takeWord_eval d₁ width counter temporary source destination value present
    distinct hvp word rest
    (by simpa [d₁, clearStacks, hsd] using hs)
    (by simpa [d₁, clearStacks, hcd] using hc)
    (by simpa [d₁, clearStacks, htd] using ht)
    (by simpa [d₁, clearStacks, hwd] using hw)
  have he : afterTake d₁ source destination value present word rest =
      replaced d source destination value present word rest := by
    apply state_ext
    · simp [d₁, afterTake, replaced, readRegs_reset]
    · funext j
      by_cases hd : j = destination
      · subst j
        simp [d₁, afterTake, replaced, clearStacks]
      · by_cases hsrc : j = source
        · subst j
          simp [d₁, afterTake, replaced, clearStacks, hsd]
        · simp [d₁, afterTake, replaced, clearStacks, hd, hsrc]
  rw [he] at h₂
  convert h₁.seq h₂ using 1
  all_goals omega

def load {r s : ℕ} (width counter temporary source : Fin s)
    (value present : Fin r) : List (Fin s) → Cmd r s
  | [] => .base .skip
  | destination :: destinations =>
      .seq (replaceWord width counter temporary source destination value present)
        (load width counter temporary source value present destinations)

def payload {s : ℕ} (words : List (Fin s × List Bool)) : List Bool :=
  words.flatMap Prod.snd

def loaded {r s : ℕ} (source : Fin s) (value present : Fin r)
    (rest : List Bool) (d : State r s) : List (Fin s × List Bool) → State r s
  | [] => d
  | (destination, word) :: words =>
      loaded source value present rest
        (replaced d source destination value present word (payload words ++ rest)) words

theorem load_eval {r s : ℕ} (width counter temporary source : Fin s)
    (value present : Fin r) (hvp : value ≠ present)
    (words : List (Fin s × List Bool))
    (distinct : ∀ item ∈ words, Function.Injective
      (![width, counter, temporary, source, item.1] : Fin 5 → Fin s))
    (nodup : (words.map Prod.fst).Nodup)
    (d : State r s) (rest : List Bool) (B : ℕ)
    (hs : d.stacks source = payload words ++ rest)
    (hc : d.stacks counter = []) (ht : d.stacks temporary = [])
    (hw : (d.stacks width).length = B)
    (hwords : ∀ item ∈ words, item.2.length = B ∧ (d.stacks item.1).length = B) :
    Eval (load width counter temporary source value present (words.map Prod.fst))
      (words.length * (16 * B + 14)) d (loaded source value present rest d words) := by
  induction words generalizing d with
  | nil =>
      simpa only [load, loaded, List.map_nil, List.length_nil, Nat.zero_mul] using
        Eval.base (StructuredProgram.Eval.skip d)
  | cons item words ih =>
      rcases item with ⟨destination, word⟩
      have hd := distinct (destination, word) (by simp)
      have hn := List.nodup_cons.mp nodup
      have hlen := hwords (destination, word) (by simp)
      let d₁ := replaced d source destination value present word (payload words ++ rest)
      have hfirst := replaceWord_eval width counter temporary source destination value present
        hd hvp d word (payload words ++ rest)
        (by simpa [payload, List.append_assoc] using hs) hc ht (hw.trans hlen.1.symm)
      have hsd : source ≠ destination := hd.ne (by decide : (3 : Fin 5) ≠ 4)
      have hcs : counter ≠ source := hd.ne (by decide : (1 : Fin 5) ≠ 3)
      have hcd : counter ≠ destination := hd.ne (by decide : (1 : Fin 5) ≠ 4)
      have hts : temporary ≠ source := hd.ne (by decide : (2 : Fin 5) ≠ 3)
      have htd : temporary ≠ destination := hd.ne (by decide : (2 : Fin 5) ≠ 4)
      have hws : width ≠ source := hd.ne (by decide : (0 : Fin 5) ≠ 3)
      have hwd : width ≠ destination := hd.ne (by decide : (0 : Fin 5) ≠ 4)
      have htail := ih
        (fun a ha => distinct a (by simp [ha])) hn.2 d₁
        (by simp [d₁, replaced, hsd])
        (by simpa [d₁, replaced, hcs, hcd] using hc)
        (by simpa [d₁, replaced, hts, htd] using ht)
        (by simpa [d₁, replaced, hws, hwd] using hw)
        (by
          intro a ha
          have hlength := hwords a (by simp [ha])
          have had : a.1 ≠ destination := by
            intro h
            apply hn.1
            exact List.mem_map.mpr ⟨a, ha, h⟩
          have has : a.1 ≠ source :=
            (distinct a (by simp [ha])).ne (by decide : (4 : Fin 5) ≠ 3)
          simpa [d₁, replaced, had, has] using hlength)
      have hrun := hfirst.seq htail
      simpa only [load, loaded, List.map_cons, List.length_cons, hlen.1, hlen.2,
        Nat.add_mul, Nat.one_mul, d₁, show 2 * B + 14 * B + 14 = 16 * B + 14 by omega,
        Nat.add_comm] using hrun

theorem loaded_stack_frame {r s : ℕ} (source : Fin s) (value present : Fin r)
    (rest : List Bool) (d : State r s) (words : List (Fin s × List Bool))
    (j : Fin s) (hsource : j ≠ source) (hwords : j ∉ words.map Prod.fst) :
    (loaded source value present rest d words).stacks j = d.stacks j := by
  induction words generalizing d with
  | nil => rfl
  | cons item words ih =>
      have hn : j ≠ item.1 ∧ j ∉ words.map Prod.fst := by
        simpa only [List.map_cons, List.mem_cons, not_or] using hwords
      rw [loaded, ih _ hn.2]
      simp [replaced, hn.1, hsource]

theorem loaded_stack_source {r s : ℕ} (source : Fin s) (value present : Fin r)
    (rest : List Bool) (d : State r s) (words : List (Fin s × List Bool))
    (hsource : source ∉ words.map Prod.fst)
    (hs : d.stacks source = payload words ++ rest) :
    (loaded source value present rest d words).stacks source = rest := by
  induction words generalizing d with
  | nil => simpa [loaded, payload] using hs
  | cons item words ih =>
      have hj : source ≠ item.1 := by
        intro h
        apply hsource
        simp [h]
      have ht : source ∉ words.map Prod.fst := fun h => hsource (by simp [h])
      apply ih _ ht
      simp [replaced, hj]

theorem loaded_stack_member {r s : ℕ} (source : Fin s) (value present : Fin r)
    (rest : List Bool) (d : State r s) (words : List (Fin s × List Bool))
    (nodup : (words.map Prod.fst).Nodup) (hsource : source ∉ words.map Prod.fst)
    (item : Fin s × List Bool) (hitem : item ∈ words) :
    (loaded source value present rest d words).stacks item.1 = item.2 := by
  induction words generalizing d with
  | nil => simp at hitem
  | cons head words ih =>
      have hn := List.nodup_cons.mp nodup
      have ht : source ∉ words.map Prod.fst := fun h => hsource (by simp [h])
      rcases List.mem_cons.mp hitem with h | h
      · subst item
        rw [loaded, loaded_stack_frame source value present rest _ words head.1]
        · simp [replaced]
        · intro hs
          apply hsource
          simp [hs]
        · exact hn.1
      · exact ih _ hn.2 ht h

theorem loaded_register_frame {r s : ℕ} (source : Fin s) (value present : Fin r)
    (rest : List Bool) (d : State r s) (words : List (Fin s × List Bool))
    (j : Fin r) (hjv : j ≠ value) (hjp : j ≠ present) :
    (loaded source value present rest d words).regs j = d.regs j := by
  induction words generalizing d with
  | nil => rfl
  | cons item words ih =>
      rw [loaded, ih]
      exact readRegs_frame d.regs value present j none hjv hjp

theorem loaded_stack_length {r s : ℕ} (source : Fin s) (value present : Fin r)
    (rest : List Bool) (d : State r s) (words : List (Fin s × List Bool))
    (B : ℕ) (j : Fin s) (hsource : j ≠ source)
    (hinitial : (d.stacks j).length = B)
    (hwords : ∀ item ∈ words, item.2.length = B) :
    ((loaded source value present rest d words).stacks j).length = B := by
  induction words generalizing d with
  | nil => exact hinitial
  | cons item words ih =>
      apply ih
      · by_cases h : j = item.1
        · simpa [replaced, h] using hwords item (by simp)
        · simpa [replaced, h, hsource] using hinitial
      · exact fun a ha => hwords a (by simp [ha])

theorem payload_length {s : ℕ} (words : List (Fin s × List Bool)) (B : ℕ)
    (hwords : ∀ item ∈ words, item.2.length = B) :
    (payload words).length = words.length * B := by
  induction words with
  | nil => simp [payload]
  | cons item words ih =>
      have hw := hwords item (by simp)
      have ht := ih (fun a ha => hwords a (by simp [ha]))
      simp only [payload, List.flatMap_cons, List.length_append, List.length_cons,
        Nat.add_mul, Nat.one_mul] at *
      omega

/-- Restore the parser's reversed payload, then load the statically assigned
words. The payload and the forward input stack are consumed. -/
abbrev readRecord {r s : ℕ} (width counter temporary source input : Fin s)
    (value present : Fin r) (destinations : List (Fin s)) : Cmd r s :=
  .seq (.call (transferProgram input source value present))
    (load width counter temporary source value present destinations)

theorem readRecord_eval {r s : ℕ} (width counter temporary source input : Fin s)
    (value present : Fin r) (hvp : value ≠ present)
    (hinput : input ≠ source) (hwidthInput : width ≠ input)
    (hcounterInput : counter ≠ input) (htemporaryInput : temporary ≠ input)
    (words : List (Fin s × List Bool))
    (distinct : ∀ item ∈ words, Function.Injective
      (![width, counter, temporary, source, item.1] : Fin 5 → Fin s))
    (nodup : (words.map Prod.fst).Nodup) (hinputWords : input ∉ words.map Prod.fst)
    (d : State r s) (B : ℕ)
    (hs : d.stacks source = []) (hi : d.stacks input = (payload words).reverse)
    (hc : d.stacks counter = []) (ht : d.stacks temporary = [])
    (hw : (d.stacks width).length = B)
    (hwords : ∀ item ∈ words, item.2.length = B ∧ (d.stacks item.1).length = B)
    (hwidthSource : width ≠ source) (hcounterSource : counter ≠ source)
    (htemporarySource : temporary ≠ source) :
    Eval (readRecord width counter temporary source input value present (words.map Prod.fst))
      (words.length * (19 * B + 14) + 3) d
      (loaded source value present [] (afterTransfer d input source value present) words) := by
  let d₁ := afterTransfer d input source value present
  have htransfer := transfer_eval d input source value present hinput hvp
  have hsource : d₁.stacks source = payload words ++ [] := by
    simp [d₁, afterTransfer, transferStacks, hi, hs]
  have hc' : d₁.stacks counter = [] := by
    simpa [d₁, afterTransfer, transferStacks, hcounterInput, hcounterSource] using hc
  have ht' : d₁.stacks temporary = [] := by
    simpa [d₁, afterTransfer, transferStacks, htemporaryInput, htemporarySource] using ht
  have hw' : (d₁.stacks width).length = B := by
    simpa [d₁, afterTransfer, transferStacks, hwidthInput, hwidthSource] using hw
  have hwords' : ∀ item ∈ words, item.2.length = B ∧ (d₁.stacks item.1).length = B := by
    intro item hitem
    have hsource' : item.1 ≠ source :=
      (distinct item hitem).ne (by decide : (4 : Fin 5) ≠ 3)
    have hinput' : item.1 ≠ input := by
      intro he
      apply hinputWords
      exact List.mem_map.mpr ⟨item, hitem, he⟩
    simpa [d₁, afterTransfer, transferStacks, hsource', hinput'] using hwords item hitem
  have hload := load_eval width counter temporary source value present hvp words
    distinct nodup d₁ [] B hsource hc' ht' hw' hwords'
  have hlength := payload_length words B (fun item hitem => (hwords item hitem).1)
  have hrun := htransfer.seq hload
  simp only [hi, List.length_reverse, hlength] at hrun
  convert hrun using 1
  all_goals ring

end SubexponentialSAT.SubexpQuarticRecordLoad

end OAI.Algorithms
