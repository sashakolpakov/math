import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBlueprintPacking

namespace OAI.Algorithms

/-! Actual framed-list loops for the raw factor builder. These are control
lemmas; the factor execution proof instantiates the body with concrete calls. -/

namespace SubexponentialSAT.SubexpBlueprintTraversal

open BitProgram StructuredCalls SubexpScanPrimitives SubexpBlueprintFactor
open SubexpBlueprintBetaServices SubexpBlueprintPacking

def inputState (ctx : Context) (regs : Fin 8 → Bool) (w : Work) (input : List Bool) : Data :=
  state ctx regs {w with input := input}

theorem unframe_work (ctx : Context) (regs : Fin 8 → Bool) (w : Work)
    (bits rest : List Bool) (hp : w.parser = []) :
    Eval unframe (9*bits.length+7)
      (inputState ctx regs w (Encoding.frame bits ++ rest))
      (inputState ctx (readRegs regs 0 1 none) w (bits ++ rest)) := by
  have h := unframe_eval (inputState ctx regs w (Encoding.frame bits ++ rest)) bits rest rfl hp
  have he : parserEffect (inputState ctx regs w (Encoding.frame bits ++ rest)) false false
      (bits ++ rest) [] = inputState ctx (readRegs regs 0 1 none) w (bits ++ rest) := by
    apply state_ext
    · rfl
    · change Function.update
        (Function.update (state ctx regs (put .input (Encoding.frame bits ++ rest) w)).stacks
          Field.input.port (bits ++ rest)) Field.parser.port [] =
        (state ctx regs (put .input (bits ++ rest) w)).stacks
      rw [← state_put, ← state_put, put_put]
      simpa only [put] using congrArg
        (fun parser => (state ctx regs {w with input := bits ++ rest, parser := parser}).stacks)
        hp.symm
  simpa only [he] using h

theorem popTag_work (ctx : Context) (regs : Fin 8 → Bool) (w : Work)
    (bit : Bool) (rest : List Bool) :
    Eval popTag 1 (inputState ctx regs w (bit :: rest))
      (inputState ctx (readRegs regs 0 1 (some bit)) w rest) := by
  let d := inputState ctx regs w (bit :: rest)
  have hinput : d.stacks 100 = bit :: rest := rfl
  have hregs : d.regs = regs := rfl
  have h := Eval.base (StructuredProgram.Eval.atom (.pop (100 : Fin 128) (0 : Fin 8) 1) d)
  have he : (⟨readRegs regs 0 1 (some bit),Function.update d.stacks 100 rest⟩ : Data) =
      inputState ctx (readRegs regs 0 1 (some bit)) w rest := by
    apply state_ext
    · rfl
    · exact (state_put ctx (readRegs regs 0 1 (some bit))
        {w with input := bit :: rest} .input rest).symm
  simpa only [popTag,atom,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,hregs,
    hinput,List.head?_cons,List.tail_cons,he] using h

def afterTag {α : Type*} (ctx : Context) (regs : Fin 8 → Bool) (w : Work)
    (encode : α → List Bool) (xs : List α) (rest : List Bool) : Data :=
  match xs with
  | [] => inputState ctx (readRegs regs 0 1 (some false)) w rest
  | x :: xs => inputState ctx (readRegs regs 0 1 (some true)) w
      (Encoding.frame (encode x) ++ (Encoding.encodeList encode xs ++ rest))

theorem popList_work {α : Type*} (ctx : Context) (regs : Fin 8 → Bool) (w : Work)
    (encode : α → List Bool) (xs : List α) (rest : List Bool) :
    Eval popTag 1 (inputState ctx regs w (Encoding.encodeList encode xs ++ rest))
      (afterTag ctx regs w encode xs rest) := by
  cases xs with
  | nil => simpa only [Encoding.encodeList,List.singleton_append,afterTag] using
      popTag_work ctx regs w false rest
  | cons x xs =>
      simpa only [Encoding.encodeList,List.cons_append,List.append_assoc,afterTag] using
        popTag_work ctx regs w true
          (Encoding.frame (encode x) ++ (Encoding.encodeList encode xs ++ rest))

def scanBudget {α : Type*} (encode : α → List Bool) (cost : α → ℕ) (xs : List α) : ℕ :=
  (xs.map (fun x => 9*(encode x).length+cost x+9)).sum

/-- A concrete body trace is executed once per framed record, in source
order. The only recursion here proves the finite program's while loop. -/
theorem scan_work {α : Type*} (ctx : Context) (body : Code)
    (encode : α → List Bool) (cost : α → ℕ) (update : α → Work → Work)
    (inv : Work → Prop) (hparser : ∀ w, inv w → w.parser = [])
    (hbody : ∀ x regs w rest, inv w →
      ∃ n rf, n ≤ cost x ∧ Eval body n
        (inputState ctx regs w (encode x ++ rest))
        (inputState ctx rf (update x w) rest))
    (hpreserve : ∀ x w, inv w → inv (update x w))
    (xs : List α) (regs : Fin 8 → Bool) (w : Work) (rest : List Bool) (hw : inv w) :
    ∃ n rf, n ≤ 2+scanBudget encode cost xs ∧
      Eval (scan body) n (inputState ctx regs w (Encoding.encodeList encode xs ++ rest))
        (inputState ctx rf (xs.foldl (fun w x => update x w) w) rest) := by
  have loop : ∀ (xs : List α) regs w, inv w →
      ∃ n rf, n ≤ 1+scanBudget encode cost xs ∧
        Eval (.while 0 (.seq unframe (.seq body popTag))) n
          (afterTag ctx regs w encode xs rest)
          (inputState ctx rf (xs.foldl (fun w x => update x w) w) rest) := by
    intro xs
    induction xs with
    | nil =>
      intro regs w hw
      refine ⟨1,readRegs regs 0 1 (some false),by simp [scanBudget],?_⟩
      exact Eval.while_false rfl
    | cons x xs ih =>
      intro regs w hw
      let rp := readRegs regs 0 1 (some true)
      let rb := readRegs rp 0 1 none
      let tail := Encoding.encodeList encode xs ++ rest
      have hu := unframe_work ctx rp w (encode x) tail (hparser w hw)
      obtain ⟨nb,rf,hnb,hb⟩ := hbody x rb w tail hw
      have hp := popList_work ctx rf (update x w) encode xs rest
      obtain ⟨nt,rt,hnt,ht⟩ := ih rf (update x w) (hpreserve x w hw)
      have h := Eval.while_true
        (by rfl : (afterTag ctx regs w encode (x :: xs) rest).regs 0 = true)
        (Eval.seq hu (Eval.seq hb hp)) ht
      refine ⟨_,rt,?_,h⟩
      simp only [scanBudget,List.map_cons,List.sum_cons] at *
      omega
  obtain ⟨n,rf,hn,h⟩ := loop xs regs w hw
  refine ⟨1+n,rf,by omega,?_⟩
  exact Eval.seq (popList_work ctx regs w encode xs rest) h

end SubexponentialSAT.SubexpBlueprintTraversal

end OAI.Algorithms
