import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.FactorBlueprint
import OAI.Algorithms.SubexponentialSAT.SubexpInputFrames
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Actual parallel traversal of the binary labels and incidence prefixes of
one factor row. The complete Lagrange cache is retained throughout. -/

namespace SubexponentialSAT.Subexp.FactorPacketCoordinates

open BitProgram StructuredCalls

abbrev Word := List Bool
abbrev Data := State 8 14

structure Prefix where
  origin : List Word
  taylor : List (List Word)

def originBytes (p : Prefix) : Word := Encoding.encodeList id p.origin
def taylorBytes (p : Prefix) : Word := Encoding.encodeList (Encoding.encodeList id) p.taylor
def prefixBytes (p : Prefix) : Word :=
  LagrangePacketProgram.incidenceFields (originBytes p) (taylorBytes p)

def cacheBytes (cache : List (List Word)) : Word :=
  ProgramEncoding.encodeRecords (cache.map (Encoding.encodeList id))

def coordinate (cache : List (List Word)) (pair : Word × Prefix) : FactorBlueprint.Coordinate :=
  ⟨pair.2.origin, pair.2.taylor, cache.getD (CounterPrograms.value pair.1) []⟩

def store (cache labels prefixes acc label captured saved : Word) : Fin 14 → Word :=
  ![label, captured, [], [], [], [], [], cache, [], [], saved, acc, labels, prefixes]

def state (regs : Fin 8 → Bool) (cache labels prefixes acc label captured saved : Word) : Data :=
  ⟨regs, store cache labels prefixes acc label captured saved⟩

def resting (regs : Fin 8 → Bool) (cache labels prefixes acc : Word) : Data :=
  state regs cache labels prefixes acc [] [] []

private theorem store_eq (cache labels prefixes acc label captured saved : Word) :
    store cache labels prefixes acc label captured saved = fun i =>
      if i = 0 then label else if i = 1 then captured else if i = 7 then cache
      else if i = 10 then saved else if i = 11 then acc else if i = 12 then labels
      else if i = 13 then prefixes else [] := by
  funext i; fin_cases i <;> rfl

def callbackPorts : Fin 12 → Fin 14 := Fin.castAdd 2
theorem callbackPorts_injective : Function.Injective callbackPorts := Fin.castAdd_injective _ _

abbrev select : Cmd 8 14 :=
  .call (ProgramLinking.liftProgram LagrangePacketBinary.program id callbackPorts)

private theorem embed_callback (regs oldRegs : Fin 8 → Bool)
    (cache labels prefixes acc label captured saved oldAcc oldLabel oldCaptured oldSaved : Word) :
    embedState id callbackPorts (state oldRegs cache labels prefixes oldAcc oldLabel oldCaptured oldSaved)
      (LagrangePacketProgram.state regs label captured [] cache [] saved acc) =
      state regs cache labels prefixes acc label captured saved := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id callbackPorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i, rfl⟩).elim
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h0 : i ≠ 0 := fun h => hi ⟨0, h.symm⟩
    have h1 : i ≠ 1 := fun h => hi ⟨1, h.symm⟩
    have h10 : i ≠ 10 := fun h => hi ⟨10, h.symm⟩
    have h11 : i ≠ 11 := fun h => hi ⟨11, h.symm⟩
    simp only [state, store_eq, h0, h1, h10, h11, ite_false]

def selectionCost (cache : List (List Word)) (pair : Word × Prefix) : ℕ :=
  LagrangePacketBinary.cost
    ((cache.take (CounterPrograms.value pair.1)).map (Encoding.encodeList id))
    (Encoding.encodeList id (cache.getD (CounterPrograms.value pair.1) []))
    ((cache.drop (CounterPrograms.value pair.1 + 1)).map (Encoding.encodeList id))
    (prefixBytes pair.2) pair.1

theorem select_eval (regs : Fin 8 → Bool) (cache : List (List Word))
    (pair : Word × Prefix) (labels prefixes acc : Word)
    (hlabel : CounterPrograms.value pair.1 < cache.length) :
    ∃ t ≤ selectionCost cache pair, ∃ rf,
      Eval select t
        (state regs (cacheBytes cache) labels prefixes acc pair.1 [] (prefixBytes pair.2).reverse)
        (resting rf (cacheBytes cache) labels prefixes
          (TupleProgram.prependRecord (FactorBlueprint.encodeCoordinate (coordinate cache pair)) acc)) := by
  obtain ⟨rf, t, ht, htrace⟩ := FactorBlueprint.selected_packet_runsIn id cache
    ⟨CounterPrograms.value pair.1, hlabel⟩ (originBytes pair.2) (taylorBytes pair.2)
    pair.1 acc rfl regs
  have h := eval_call_lifted LagrangePacketBinary.program id callbackPorts
    (state regs (cacheBytes cache) labels prefixes acc pair.1 [] (prefixBytes pair.2).reverse)
    Function.injective_id callbackPorts_injective htrace
  change Eval select t
    (embedState id callbackPorts
      (state regs (cacheBytes cache) labels prefixes acc pair.1 [] (prefixBytes pair.2).reverse)
      (LagrangePacketProgram.state regs pair.1 [] [] (cacheBytes cache) []
        (prefixBytes pair.2).reverse acc))
    (embedState id callbackPorts
      (state regs (cacheBytes cache) labels prefixes acc pair.1 [] (prefixBytes pair.2).reverse)
      (LagrangePacketProgram.state rf [] [] [] (cacheBytes cache) [] []
        (TupleProgram.prependRecord (FactorBlueprint.encodeCoordinate (coordinate cache pair)) acc))) at h
  rw [embed_callback, embed_callback] at h
  refine ⟨t, ht, rf, ?_⟩
  simpa only [select, resting, cacheBytes, prefixBytes, coordinate,
    FactorBlueprint.encodeCoordinate, FactorBlueprint.originBytes,
    FactorBlueprint.taylorBytes, FactorBlueprint.coefficientBytes, originBytes, taylorBytes] using h

abbrev readLabel : Cmd 8 14 := SubexpInputFrames.readField 12 1 (by decide)
abbrev moveLabel : Cmd 8 14 := .call (StackRoutines.transferProgram 1 0 0 1)
abbrev readPrefix : Cmd 8 14 := SubexpInputFrames.readField 13 10 (by decide)

theorem readLabel_eval (regs : Fin 8 → Bool) (cache bits labels prefixes acc : Word) :
    ∃ rf, Eval readLabel (6 * bits.length + 4)
      (resting regs cache (Encoding.frame bits ++ labels) prefixes acc)
      (state rf cache labels prefixes acc [] bits.reverse []) := by
  obtain ⟨e, he, hs⟩ := SubexpInputFrames.readField_execute 12 1 (by decide)
    (resting regs cache (Encoding.frame bits ++ labels) prefixes acc) bits labels rfl rfl
  have heq : e = state e.regs cache labels prefixes acc [] bits.reverse [] := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · rw [hs]
      funext i
      by_cases h1 : i = 1 <;> by_cases h12 : i = 12 <;>
        simp [state, resting, store_eq, h1, h12]
  exact ⟨e.regs, by rw [heq] at he; exact he⟩

theorem moveLabel_eval (regs : Fin 8 → Bool) (cache bits labels prefixes acc : Word) :
    Eval moveLabel (3 * bits.length + 3)
      (state regs cache labels prefixes acc [] bits.reverse [])
      (state (readRegs regs 0 1 none) cache labels prefixes acc bits [] []) := by
  have h := ListRegisterProgram.transfer_run (1 : Fin 14) 0 (0 : Fin 8) 1
    (by decide) (by decide) regs (store cache labels prefixes acc [] bits.reverse [])
  have hs : StackRoutines.transferStacks (1 : Fin 14) 0
      (store cache labels prefixes acc [] bits.reverse []) =
      store cache labels prefixes acc bits [] [] := by
    funext i; fin_cases i <;> simp [StackRoutines.transferStacks, store]
  have hl : (store cache labels prefixes acc [] bits.reverse [] 1).length = bits.length := by
    simp [store]
  rw [hs, hl] at h
  apply Eval.call
  exact h

theorem readPrefix_eval (regs : Fin 8 → Bool) (cache label bits labels prefixes acc : Word) :
    ∃ rf, Eval readPrefix (6 * bits.length + 4)
      (state regs cache labels (Encoding.frame bits ++ prefixes) acc label [] [])
      (state rf cache labels prefixes acc label [] bits.reverse) := by
  obtain ⟨e, he, hs⟩ := SubexpInputFrames.readField_execute 13 10 (by decide)
    (state regs cache labels (Encoding.frame bits ++ prefixes) acc label [] []) bits prefixes rfl rfl
  have heq : e = state e.regs cache labels prefixes acc label [] bits.reverse := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · rw [hs]
      funext i
      by_cases h10 : i = 10 <;> by_cases h13 : i = 13 <;>
        simp [state, store_eq, h10, h13]
  exact ⟨e.regs, by rw [heq] at he; exact he⟩

abbrev pairCommand : Cmd 8 14 := .seq readLabel (.seq moveLabel (.seq readPrefix select))

def pairCost (cache : List (List Word)) (pair : Word × Prefix) : ℕ :=
  9 * pair.1.length + 6 * (prefixBytes pair.2).length + 11 + selectionCost cache pair

theorem pair_eval (regs : Fin 8 → Bool) (cache : List (List Word))
    (pair : Word × Prefix) (labels prefixes acc : Word)
    (hlabel : CounterPrograms.value pair.1 < cache.length) :
    ∃ t ≤ pairCost cache pair, ∃ rf,
      Eval pairCommand t
        (resting regs (cacheBytes cache) (Encoding.frame pair.1 ++ labels)
          (Encoding.frame (prefixBytes pair.2) ++ prefixes) acc)
        (resting rf (cacheBytes cache) labels prefixes
          (TupleProgram.prependRecord (FactorBlueprint.encodeCoordinate (coordinate cache pair)) acc)) := by
  obtain ⟨r1, h1⟩ := readLabel_eval regs (cacheBytes cache) pair.1 labels
    (Encoding.frame (prefixBytes pair.2) ++ prefixes) acc
  have h2 := moveLabel_eval r1 (cacheBytes cache) pair.1 labels
    (Encoding.frame (prefixBytes pair.2) ++ prefixes) acc
  obtain ⟨r3, h3⟩ := readPrefix_eval (readRegs r1 0 1 none) (cacheBytes cache) pair.1
    (prefixBytes pair.2) labels prefixes acc
  obtain ⟨t, ht, rf, h4⟩ := select_eval r3 cache pair labels prefixes acc hlabel
  refine ⟨_, ?_, rf, h1.seq (h2.seq (h3.seq h4))⟩
  unfold pairCost
  omega

abbrev tags : Cmd 8 14 := .seq (SubexpInputFrames.readTag 12)
  (.base (.atom (.pop 13 0 1)))

theorem tags_eval (regs : Fin 8 → Bool) (flag : Bool) (cache labels prefixes acc : Word) :
    ∃ rf, Eval tags 2 (resting regs cache (flag :: labels) (flag :: prefixes) acc)
      (resting rf cache labels prefixes acc) ∧ rf 7 = flag := by
  obtain ⟨e, he, hs, hf⟩ := SubexpInputFrames.readTag_execute 12
    (resting regs cache (flag :: labels) (flag :: prefixes) acc) flag labels rfl
  have heq : e = resting e.regs cache labels (flag :: prefixes) acc := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · rw [hs]
      funext i
      by_cases h12 : i = 12 <;>
        simp [state, resting, store_eq, h12]
  rw [heq] at he
  let rf := readRegs e.regs 0 1 (some flag)
  have hp : Eval (.base (.atom (.pop 13 0 1))) 1
      (resting e.regs cache labels (flag :: prefixes) acc)
      (resting rf cache labels prefixes acc) := by
    have h := StructuredProgram.Eval.atom (.pop (13 : Fin 14) (0 : Fin 8) 1)
      (resting e.regs cache labels (flag :: prefixes) acc)
    have hstate : (StructuredProgram.Atom.pop (13 : Fin 14) (0 : Fin 8) 1).eval
        (resting e.regs cache labels (flag :: prefixes) acc) =
        resting rf cache labels prefixes acc := by
      apply SubexpScanPrimitives.state_ext
      · rfl
      · change Function.update (store cache labels (flag :: prefixes) acc [] [] []) 13 prefixes =
          store cache labels prefixes acc [] [] []
        funext i
        by_cases h13 : i = 13 <;> simp [store_eq, h13]
    rw [hstate] at h
    exact .base h
  exact ⟨rf, he.seq hp, by simpa [rf, readRegs] using hf⟩

def labelsBytes (pairs : List (Word × Prefix)) : Word := Encoding.encodeList Prod.fst pairs
def prefixesBytes (pairs : List (Word × Prefix)) : Word :=
  Encoding.encodeList (fun pair => prefixBytes pair.2) pairs

def flag : List (Word × Prefix) → Bool
  | [] => false
  | _ :: _ => true

def labelsAfter : List (Word × Prefix) → Word → Word
  | [], tail => tail
  | pair :: rest, tail => Encoding.frame pair.1 ++ (labelsBytes rest ++ tail)
def prefixesAfter : List (Word × Prefix) → Word → Word
  | [], tail => tail
  | pair :: rest, tail => Encoding.frame (prefixBytes pair.2) ++ (prefixesBytes rest ++ tail)

theorem labels_tag (pairs : List (Word × Prefix)) (tail : Word) :
    labelsBytes pairs ++ tail = flag pairs :: labelsAfter pairs tail := by
  cases pairs <;> simp [labelsBytes, labelsAfter, flag, Encoding.encodeList, List.append_assoc]
theorem prefixes_tag (pairs : List (Word × Prefix)) (tail : Word) :
    prefixesBytes pairs ++ tail = flag pairs :: prefixesAfter pairs tail := by
  cases pairs <;> simp [prefixesBytes, prefixesAfter, flag, Encoding.encodeList, List.append_assoc]

abbrev loop : Cmd 8 14 := .while 7 (.seq pairCommand tags)
abbrev command : Cmd 8 14 := .seq tags loop

def budget (cache : List (List Word)) : List (Word × Prefix) → ℕ
  | [] => 0
  | pair :: rest => pairCost cache pair + 3 + budget cache rest

theorem loop_eval (cache : List (List Word)) (pairs : List (Word × Prefix))
    (valid : ∀ pair ∈ pairs, CounterPrograms.value pair.1 < cache.length)
    (regs : Fin 8 → Bool) (labelsTail prefixesTail : Word) (acc : List FactorBlueprint.Coordinate)
    (hg : regs 7 = flag pairs) :
    ∃ t ≤ budget cache pairs + 1, ∃ rf,
      Eval loop t
        (resting regs (cacheBytes cache) (labelsAfter pairs labelsTail)
          (prefixesAfter pairs prefixesTail) (Encoding.encodeList FactorBlueprint.encodeCoordinate acc))
        (resting rf (cacheBytes cache) labelsTail prefixesTail
          (Encoding.encodeList FactorBlueprint.encodeCoordinate
            ((pairs.map (coordinate cache)).reverse ++ acc))) := by
  induction pairs generalizing regs acc with
  | nil =>
      refine ⟨1, by simp [budget], regs, ?_⟩
      simpa only [labelsAfter, prefixesAfter, List.map_nil, List.reverse_nil, List.nil_append] using
        (Eval.while_false (body := .seq pairCommand tags)
          (a := resting regs (cacheBytes cache) labelsTail prefixesTail
            (Encoding.encodeList FactorBlueprint.encodeCoordinate acc)) hg)
  | cons pair rest ih =>
      obtain ⟨np, hnp, rp, hp⟩ := pair_eval regs cache pair
        (labelsBytes rest ++ labelsTail) (prefixesBytes rest ++ prefixesTail)
        (Encoding.encodeList FactorBlueprint.encodeCoordinate acc) (valid pair (by simp))
      change Eval pairCommand np _ (resting rp (cacheBytes cache)
        (labelsBytes rest ++ labelsTail) (prefixesBytes rest ++ prefixesTail)
        (Encoding.encodeList FactorBlueprint.encodeCoordinate (coordinate cache pair :: acc))) at hp
      obtain ⟨rt, ht, hrt⟩ := tags_eval rp (flag rest) (cacheBytes cache)
        (labelsAfter rest labelsTail) (prefixesAfter rest prefixesTail)
        (Encoding.encodeList FactorBlueprint.encodeCoordinate (coordinate cache pair :: acc))
      rw [← labels_tag, ← prefixes_tag] at ht
      obtain ⟨nr, hnr, rf, hr⟩ := ih (fun p h => valid p (by simp [h])) rt
        (coordinate cache pair :: acc) hrt
      refine ⟨np + 2 + nr + 1, ?_, rf, ?_⟩
      · simp only [budget]
        omega
      · have h := Eval.while_true (by exact hg) (hp.seq ht) hr
        simpa only [loop, labelsAfter, prefixesAfter, List.map_cons, List.reverse_cons,
          List.append_assoc, List.singleton_append] using h

def program := compiled command (12 : Fin 14) 11

theorem program_runsIn (cache : List (List Word)) (pairs : List (Word × Prefix))
    (valid : ∀ pair ∈ pairs, CounterPrograms.value pair.1 < cache.length)
    (regs : Fin 8 → Bool) (labelsTail prefixesTail : Word) (acc : List FactorBlueprint.Coordinate) :
    ∃ rf, RunsIn program (budget cache pairs + 4)
      ((resting regs (cacheBytes cache) (labelsBytes pairs ++ labelsTail)
        (prefixesBytes pairs ++ prefixesTail)
        (Encoding.encodeList FactorBlueprint.encodeCoordinate acc)).withPC (some program.entry))
      ((resting rf (cacheBytes cache) labelsTail prefixesTail
        (Encoding.encodeList FactorBlueprint.encodeCoordinate
          ((pairs.map (coordinate cache)).reverse ++ acc))).withPC none) := by
  obtain ⟨rt, ht, hrt⟩ := tags_eval regs (flag pairs) (cacheBytes cache)
    (labelsAfter pairs labelsTail) (prefixesAfter pairs prefixesTail)
    (Encoding.encodeList FactorBlueprint.encodeCoordinate acc)
  rw [← labels_tag, ← prefixes_tag] at ht
  obtain ⟨n, hn, rf, he⟩ := loop_eval cache pairs valid rt labelsTail prefixesTail acc hrt
  refine ⟨rf, 2 + n + 1, by omega, ?_⟩
  exact compiled_halt_trace (ht.seq he) 12 11

theorem primitive_execution (cache : List (List Word)) (pairs : List (Word × Prefix))
    (valid : ∀ pair ∈ pairs, CounterPrograms.value pair.1 < cache.length)
    (regs : Fin 8 → Bool) (labelsTail prefixesTail : Word) (acc : List FactorBlueprint.Coordinate) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (budget cache pairs + 4))
      (primitiveCfg program ((resting regs (cacheBytes cache) (labelsBytes pairs ++ labelsTail)
        (prefixesBytes pairs ++ prefixesTail)
        (Encoding.encodeList FactorBlueprint.encodeCoordinate acc)).withPC (some program.entry)))
      (primitiveCfg program ((resting rf (cacheBytes cache) labelsTail prefixesTail
        (Encoding.encodeList FactorBlueprint.encodeCoordinate
          ((pairs.map (coordinate cache)).reverse ++ acc))).withPC none)) := by
  obtain ⟨rf, h⟩ := program_runsIn cache pairs valid regs labelsTail prefixesTail acc
  exact ⟨rf, BitProgram.primitive_execution program h⟩

end SubexponentialSAT.Subexp.FactorPacketCoordinates

end OAI.Algorithms
