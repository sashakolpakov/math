import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPacketLocal

namespace OAI.Algorithms

/-! The original-order factor mapper, proved from its actual fixed loop. -/

namespace SubexponentialSAT.SubexpFactorPacketExecution

open BitProgram StructuredCalls SubexpScanPrimitives SubexpFactorPacketControl
open SubexpFactorPacketCalls SubexpFactorPacketLocal
open Subexp.FactorPacketCoordinates (cacheBytes)

def groupStream (inputs : List Input) : Word := Encoding.encodeList groupBytes inputs
def tableStream (inputs : List Input) : Word := Encoding.encodeList Input.answers inputs
def packetStream (m : Masters) (cache : List (List Word)) (inputs : List Input) : Word :=
  Encoding.encodeList (factorBytes m cache) inputs
def packetPrefix (m : Masters) (cache : List (List Word)) (inputs : List Input) : Word :=
  inputs.flatMap (fun i => true :: Encoding.frame (factorBytes m cache i))

theorem packetPrefix_reverse_cons (m : Masters) (cache : List (List Word))
    (i : Input) (inputs : List Input) (out : Word) :
    packetPrefix m cache (i :: inputs).reverse ++ out =
      packetPrefix m cache inputs.reverse ++
        (true :: (Encoding.frame (factorBytes m cache i) ++ out)) := by
  simp [packetPrefix, List.reverse_cons, List.flatMap_append, List.append_assoc]

theorem packetPrefix_terminated (m : Masters) (cache : List (List Word)) (inputs : List Input) :
    packetPrefix m cache inputs ++ [false] = packetStream m cache inputs := by
  induction inputs with
  | nil => rfl
  | cons i inputs ih =>
      simpa only [packetPrefix, packetStream, List.flatMap_cons, List.cons_append,
        List.append_assoc, Encoding.encodeList] using
        congrArg (fun tail => true :: (Encoding.frame (factorBytes m cache i) ++ tail)) ih

def scanBudget (m : Masters) (cache : List (List Word)) : List Input → ℕ
  | [] => 3
  | i :: inputs => localBudget m cache i + scanBudget m cache inputs + 3

theorem scan_eval (regs : Fin 8 → Bool) (m : Masters) (cache : List (List Word))
    (hc : m.cache = cacheBytes cache) (hm : 0 < BinaryArithmetic.toNat m.modulus)
    (hlen : BinaryArithmetic.toNat m.modulus ≤ cache.length)
    (inputs : List Input) (acc output : Word) :
    ∃ n ≤ scanBudget m cache inputs, ∃ rf,
      Eval (.seq readTags loop) n
        (workState regs (resting m (groupStream inputs) (tableStream inputs) acc output))
        (workState rf (resting m [] [] (packetPrefix m cache inputs.reverse ++ acc) output)) := by
  induction inputs generalizing regs acc with
  | nil =>
      let v := resting m [] [] acc output
      have hr := readTags_eval regs v false false [] []
      have hl : Eval loop 1
          (workState (readRegs (readRegs regs 7 6 (some false)) 0 1 (some false)) v)
          (workState (readRegs (readRegs regs 7 6 (some false)) 0 1 (some false)) v) :=
        Eval.while_false (by simp [workState, readRegs])
      refine ⟨3, Nat.le_refl _, readRegs (readRegs regs 7 6 (some false)) 0 1 (some false), ?_⟩
      simpa only [v, resting, groupStream, tableStream, Encoding.encodeList, packetPrefix,
        List.reverse_nil, List.flatMap_nil, List.nil_append] using hr.seq hl
  | cons i inputs ih =>
      let gs := Encoding.frame (groupBytes i) ++ groupStream inputs
      let ts := Encoding.frame i.answers ++ tableStream inputs
      let v := resting m [] [] acc output
      have hr := readTags_eval regs v true true gs ts
      obtain ⟨nb, hnb, rb, hb⟩ := makeFactor_eval
        (readRegs (readRegs regs 7 6 (some true)) 0 1 (some true))
        m cache hc hm hlen i (groupStream inputs) (tableStream inputs) acc output
      obtain ⟨ns, hns, rf, hs⟩ := ih rb (true :: (Encoding.frame (factorBytes m cache i) ++ acc))
      cases hs with
      | seq hsRead hsLoop =>
          have ht := hr.seq (Eval.while_true (by simp [workState, readRegs])
            (hb.seq hsRead) hsLoop)
          refine ⟨_, ?_, rf, by
            simpa only [loop, groupStream, tableStream, Encoding.encodeList, v, resting, gs, ts,
              packetPrefix_reverse_cons] using ht⟩
          simp only [scanBudget]
          omega

def runtimeBound (m : Masters) (cache : List (List Word)) (inputs : List Input) : ℕ :=
  (7 * m.groups.length + 5) + (7 * m.tables.length + 5) + 4 +
    scanBudget m cache inputs + 10 * (packetStream m cache inputs.reverse).length + 1

theorem program_runsIn (regs : Fin 8 → Bool) (m : Masters) (cache : List (List Word))
    (hc : m.cache = cacheBytes cache) (hm : 0 < BinaryArithmetic.toNat m.modulus)
    (hlen : BinaryArithmetic.toNat m.modulus ≤ cache.length)
    (inputs : List Input) (hg : m.groups = groupStream inputs)
    (ht : m.tables = tableStream inputs) :
    ∃ rf, RunsIn program (runtimeBound m cache inputs)
      ((SubexpFactorPacketControl.state regs m).withPC (some program.entry))
      ((SubexpFactorPacketControl.outputState rf m (packetStream m cache inputs)).withPC none) := by
  let a : View := {masters := m}
  have h1 := copy_groups_eval regs a
  let b : View := {a with todoGroups := m.groups}
  have h2 := copy_tables_eval (readRegs regs 0 1 none) b
  let c : View := {b with todoTables := m.tables}
  have h3 := seed_acc_eval (readRegs (readRegs regs 0 1 none) 0 1 none) c
  let r3 := Function.update (readRegs (readRegs regs 0 1 none) 0 1 none) 0 false
  let d : View := {c with acc := [false]}
  have h4 := seed_output_eval r3 d
  let r4 := Function.update r3 0 false
  obtain ⟨ns, hns, rs, hs⟩ := scan_eval r4 m cache hc hm hlen inputs [false] [false]
  rw [packetPrefix_terminated] at hs
  let e := resting m [] [] (packetStream m cache inputs.reverse) [false]
  obtain ⟨nr, hnr, rf, h5⟩ := reverseFactors_eval rs e
    (inputs.reverse.map (factorBytes m cache))
  have hencode {A : Type} (f : A → Word) (xs : List A) :
      Encoding.encodeList id (xs.map f) = Encoding.encodeList f xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, Encoding.encodeList, id_eq, ih]
  simp only [← List.map_reverse, List.reverse_reverse] at h5
  rw [hencode (factorBytes m cache) inputs.reverse,
    hencode (factorBytes m cache) inputs] at h5
  rw [hencode (factorBytes m cache) inputs.reverse] at hnr
  have hs' : Eval (.seq readTags loop) ns
      (workState r4 {d with output := [false]}) (workState rs e) := by
    simpa only [d, c, b, a, resting, hg, ht, e] using hs
  cases hs' with
  | seq hsRead hsLoop =>
      have hall := (h1.seq (h2.seq (h3.seq h4))).seq
        (hsRead.seq (hsLoop.seq h5))
      have hfinal : workState rf {e with acc := [], output := Encoding.encodeList (factorBytes m cache) inputs} =
          SubexpFactorPacketControl.outputState rf m (packetStream m cache inputs) := by
        refine SubexpScanPrimitives.state_ext (by rfl) ?_
        funext i
        by_cases hi : i = 47 <;>
          simp [workState, workStore, e, resting, packetStream, SubexpFactorPacketControl.outputState,
            SubexpFactorPacketControl.store, hi]
      have hstart : workState regs a = SubexpFactorPacketControl.state regs m := by
        refine SubexpScanPrimitives.state_ext (by rfl) ?_
        funext j
        simp [workState, workStore, a, SubexpFactorPacketControl.state,
          SubexpFactorPacketControl.store]
      rw [hstart, hfinal] at hall
      refine ⟨rf, _, ?_, compiled_halt_trace hall 42 47⟩
      unfold runtimeBound
      change nr ≤ 10 * (packetStream m cache inputs.reverse).length at hnr
      dsimp only [a, b]
      omega

end SubexponentialSAT.SubexpFactorPacketExecution

end OAI.Algorithms
