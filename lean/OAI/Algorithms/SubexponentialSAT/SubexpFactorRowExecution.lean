import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorRowStream

namespace OAI.Algorithms

/-! Exact execution and row-order semantics of the Boolean table serializer. -/

namespace SubexponentialSAT.SubexpFactorRowStream

open BitProgram StructuredCalls SubexpScanPrimitives

def resting (modulus rank : Word) (k : ℕ) (input zero one output : Word) : View :=
  ⟨modulus, rank, List.replicate k true, input, zero, one, [], [], [], output⟩

def rawPrefix (rows : List RawRow) : Word :=
  rows.flatMap (fun row => true :: Encoding.frame (Subexp.FactorPacketRows.rawRowBytes row))

theorem rawPrefix_nil : rawPrefix [] = [] := rfl

theorem rawPrefix_cons (r : RawRow) (rows : List RawRow) :
    rawPrefix (r :: rows) = true :: (Encoding.frame (Subexp.FactorPacketRows.rawRowBytes r)
      ++ rawPrefix rows) := by
  simp [rawPrefix]

theorem rawPrefix_reverse_cons (r : RawRow) (rows : List RawRow) (out : Word) :
    rawPrefix (r :: rows).reverse ++ out = rawPrefix rows.reverse ++
      (true :: (Encoding.frame (Subexp.FactorPacketRows.rawRowBytes r) ++ out)) := by
  simp [rawPrefix, List.reverse_cons, List.flatMap_append, List.append_assoc]

theorem rawPrefix_terminated (rows : List RawRow) :
    rawPrefix rows ++ [false] = Encoding.encodeList Subexp.FactorPacketRows.rawRowBytes rows := by
  induction rows with
  | nil => rfl
  | cons r rows ih => simp only [rawPrefix_cons, List.cons_append, List.append_assoc, ih,
      Encoding.encodeList]

def rowCost (modulus : Word) (k : ℕ) (zero one rank : Word) (answer : Bool) : ℕ :=
  SubexpFactorLabelProgram.budget modulus rank k +
    15 * (if answer then one else zero).length +
    8 * (Subexp.FactorPacketRows.rawRowBytes (row modulus k zero one rank answer)).length +
    CounterPrograms.rippleCost true rank + 28

theorem body_eval (regs : Fin 8 → Bool) (modulus rank : Word) (k : ℕ)
    (input zero one output : Word) (answer : Bool) (ha : regs 0 = answer) :
    ∃ n ≤ rowCost modulus k zero one rank answer, ∃ rf,
      Eval body n (state regs (resting modulus rank k input zero one output))
        (state rf (resting modulus (CounterPrograms.ripple true rank) k input zero one
          (true :: (Encoding.frame (Subexp.FactorPacketRows.rawRowBytes
            (row modulus k zero one rank answer)) ++ output)))) := by
  let value := if answer then one else zero
  let ds := Encoding.encodeList id (SubexpBasePUnranking.digitWords modulus k rank)
  let bits := Encoding.frame value ++ ds
  let v0 := resting modulus rank k input zero one output
  let v1 : View := {v0 with value := value}
  let v2 : View := {v1 with labels := ds}
  let v3 : View := {v2 with value := [], payload := value.reverse}
  let v4 : View := {v3 with payload := [], labels := true :: bits}
  let v5 : View := {v4 with labels := bits}
  let v6 : View := {v5 with labels := [], payload := bits.reverse}
  let v7 : View := {v6 with payload := [], output := true :: (Encoding.frame bits ++ output)}
  have h1 : Eval choose (7 * value.length + 6) (state regs v0)
      (state (readRegs regs 0 1 none) v1) := by
    simpa only [v0, v1, resting, scalar, ha, value] using choose_eval regs v0 rfl
  obtain ⟨nl, hnl, r2, h2⟩ := labels_eval (readRegs regs 0 1 none) v1 k rfl rfl
  change Eval labels nl (state (readRegs regs 0 1 none) v1) (state r2 v2) at h2
  have h3 : Eval transferValue (3 * value.length + 3) (state r2 v2)
      (state (readRegs r2 0 1 none) v3) := transferValue_eval r2 v2 rfl
  have h4 : Eval (write 16) (5 * value.length + 7)
      (state (readRegs r2 0 1 none) v3)
      (state (Function.update (Function.update (readRegs r2 0 1 none) 0 true) 1 false) v4) :=
    writeValue_eval _ v3 value rfl
  let r4 := Function.update (Function.update (readRegs r2 0 1 none) 0 true) 1 false
  have h5 : Eval removeTag 1 (state r4 v4)
      (state (readRegs r4 0 1 (some true)) v5) := removeTag_eval r4 v4 bits rfl
  have h6 : Eval transferRow (3 * bits.length + 3)
      (state (readRegs r4 0 1 (some true)) v5)
      (state (readRegs (readRegs r4 0 1 (some true)) 0 1 none) v6) :=
    transferRow_eval _ v5 rfl
  let r6 := readRegs (readRegs r4 0 1 (some true)) 0 1 none
  have h7 : Eval (write 22) (5 * bits.length + 7) (state r6 v6)
      (state (Function.update (Function.update r6 0 true) 1 false) v7) :=
    writeRow_eval r6 v6 bits rfl
  let r7 := Function.update (Function.update r6 0 true) 1 false
  have h8 := increment_eval r7 v7
  have hall := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq h8))))))
  refine ⟨_, ?_, readRegs r7 0 1 none, hall⟩
  change nl ≤ SubexpFactorLabelProgram.budget modulus rank k at hnl
  change (7 * value.length + 6) + (nl + ((3 * value.length + 3) +
    ((5 * value.length + 7) + (1 + ((3 * bits.length + 3) +
    ((5 * bits.length + 7) + (CounterPrograms.rippleCost true rank + 1))))))) ≤ _
  change _ ≤ SubexpFactorLabelProgram.budget modulus rank k + 15 * value.length +
    8 * bits.length + CounterPrograms.rippleCost true rank + 28
  omega

def scanCost (modulus : Word) (k : ℕ) (zero one : Word) : Word → Word → ℕ
  | _, [] => 2
  | rank, answer :: answers => rowCost modulus k zero one rank answer +
      scanCost modulus k zero one (CounterPrograms.ripple true rank) answers + 2

theorem scan_eval (regs : Fin 8 → Bool) (modulus rank : Word) (k : ℕ)
    (input zero one output : Word) :
    ∃ n ≤ scanCost modulus k zero one rank input, ∃ rf,
      Eval (.seq readAnswer loop) n (state regs (resting modulus rank k input zero one output))
        (state rf (resting modulus (finalRank rank input) k [] zero one
          (rawPrefix (forwardRows modulus k zero one rank input).reverse ++ output))) := by
  induction input generalizing regs rank output with
  | nil =>
      have hr := readAnswer_eval regs (resting modulus rank k [] zero one output)
      have hl : Eval loop 1
          (state (readRegs regs 0 1 none) (resting modulus rank k [] zero one output))
          (state (readRegs regs 0 1 none) (resting modulus rank k [] zero one output)) :=
        Eval.while_false (by simp [state])
      refine ⟨2, Nat.le_refl _, readRegs regs 0 1 none, ?_⟩
      simpa only [resting, List.head?_nil, List.tail_nil, forwardRows, List.reverse_nil,
        rawPrefix_nil, List.nil_append, finalRank] using hr.seq hl
  | cons answer answers ih =>
      let v := resting modulus rank k (answer :: answers) zero one output
      have hr := readAnswer_eval regs v
      change Eval readAnswer 1 (state regs v)
        (state (readRegs regs 0 1 (some answer))
          (resting modulus rank k answers zero one output)) at hr
      obtain ⟨nb, hnb, rb, hb⟩ := body_eval (readRegs regs 0 1 (some answer))
        modulus rank k answers zero one output answer (by simp [readRegs])
      obtain ⟨ns, hns, rf, hs⟩ := ih rb (CounterPrograms.ripple true rank)
        (true :: (Encoding.frame (Subexp.FactorPacketRows.rawRowBytes
          (row modulus k zero one rank answer)) ++ output))
      cases hs with
      | seq hsRead hsLoop =>
          have ht := hr.seq (Eval.while_true (by simp [state]) (hb.seq hsRead) hsLoop)
          refine ⟨_, ?_, rf, by
            simpa only [v, forwardRows, finalRank, rawPrefix_reverse_cons] using ht⟩
          simp only [scanCost]
          omega

def runtimeBound (modulus : Word) (k : ℕ) (zero one answers : Word) : ℕ :=
  scanCost modulus k zero one [] answers.reverse +
    2 * (finalRank [] answers.reverse).length + 6

theorem program_runsIn (regs : Fin 8 → Bool) (modulus : Word) (k : ℕ)
    (zero one answers : Word) :
    ∃ rf, RunsIn program (runtimeBound modulus k zero one answers)
      ((state regs (resting modulus [] k answers.reverse zero one [])).withPC
        (some program.entry))
      ((state rf (resting modulus [] k [] zero one
        (Encoding.encodeList Subexp.FactorPacketRows.rawRowBytes
          (tableRows modulus k zero one answers)))).withPC none) := by
  have hseed := seed_eval regs (resting modulus [] k answers.reverse zero one []) rfl
  obtain ⟨ns, hns, rs, hs⟩ := scan_eval (Function.update regs 0 false) modulus [] k
    answers.reverse zero one [false]
  rw [rawPrefix_terminated] at hs
  change Eval (.seq readAnswer loop) ns _
    (state rs (resting modulus (finalRank [] answers.reverse) k [] zero one
      (Encoding.encodeList Subexp.FactorPacketRows.rawRowBytes
        (tableRows modulus k zero one answers)))) at hs
  have hc := clearRank_eval rs (resting modulus (finalRank [] answers.reverse) k [] zero one
    (Encoding.encodeList Subexp.FactorPacketRows.rawRowBytes
      (tableRows modulus k zero one answers)))
  cases hs with
  | seq hr hl =>
      have hall := hseed.seq (hr.seq (hl.seq hc))
      refine ⟨readRegs rs 0 1 none, _, ?_, compiled_halt_trace hall 17 22⟩
      unfold runtimeBound
      change 2 + (_ + (_ + (2 * (finalRank [] answers.reverse).length + 3))) + 1 ≤ _
      omega

end SubexponentialSAT.SubexpFactorRowStream

end OAI.Algorithms
