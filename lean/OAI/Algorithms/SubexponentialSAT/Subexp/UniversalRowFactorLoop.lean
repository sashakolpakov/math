import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowFactors
import OAI.Algorithms.SubexponentialSAT.Subexp.CollisionStreamProgram

namespace OAI.Algorithms

/-! Actual diagonal exclusion and factor-record production for a row. -/

namespace SubexponentialSAT.Subexp.UniversalRowFactorLoop

open BitProgram StructuredCalls StackRoutines
open UniversalRowGather (Data Word)

def equalityRegs : Fin 5 → Fin 8 := Fin.castAdd 3
def equalityStacks : Fin 13 → Fin 32 := Fin.castAdd 19

theorem equalityRegs_injective : Function.Injective equalityRegs := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)

theorem equalityStacks_injective : Function.Injective equalityStacks := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 32 => x.val) h)

def equalityProgram := compiled CollisionStreamProgram.sealCommand (1 : Fin 13) 11

abbrev equality : Cmd 8 32 :=
  .call (ProgramLinking.liftProgram equalityProgram equalityRegs equalityStacks)

abbrev afterEquality (a : Data) (answer : Bool) : Data :=
  ⟨fun j => if j.val < 5 then false else a.regs j,
    Function.update (Function.update (Function.update a.stacks 1 []) 12 [])
      11 (answer :: a.stacks 11)⟩

theorem equality_eval (a : Data) :
    ∃ n ≤ 11 * (a.stacks 1).length + 2 * (a.stacks 12).length + 20,
      Eval equality n a (afterEquality a (decide (a.stacks 1 = a.stacks 12))) := by
  let inner : State 5 13 := ⟨a.regs ∘ equalityRegs, a.stacks ∘ equalityStacks⟩
  obtain ⟨n, hn, ht⟩ := CollisionStreamProgram.seal_eval inner
  have hin : embedState equalityRegs equalityStacks a inner = a := by
    apply embedState_eq_of_ports _ _ _ _ _ equalityRegs_injective equalityStacks_injective
    · intros; rfl
    · intros; rfl
    · intros; rfl
    · intros; rfl
  have hout : embedState equalityRegs equalityStacks a
      (CollisionStreamProgram.sealed inner (decide (inner.stacks 1 = inner.stacks 12))) =
      afterEquality a (decide (a.stacks 1 = a.stacks 12)) := by
    apply embedState_eq_of_ports _ _ _ _ _ equalityRegs_injective equalityStacks_injective
    · intro j
      fin_cases j <;> norm_num [afterEquality, CollisionStreamProgram.sealed, equalityRegs]
    · intro j hj
      have hge : ¬ j.val < 5 := by
        intro h
        exact hj ⟨⟨j.val, h⟩, Fin.ext rfl⟩
      simp [ hge]
    · intro j
      fin_cases j <;>
        simp [ CollisionStreamProgram.sealed, inner, equalityStacks] ; rfl
    · intro j hj
      have h1 : j ≠ 1 := fun h => hj ⟨1, h.symm⟩
      have h11 : j ≠ 11 := fun h => hj ⟨11, h.symm⟩
      have h12 : j ≠ 12 := fun h => hj ⟨12, h.symm⟩
      simp [ h1, h11, h12]
  have he := eval_call_lifted equalityProgram equalityRegs equalityStacks a
    equalityRegs_injective equalityStacks_injective
    (a := inner)
    (b := CollisionStreamProgram.sealed inner (decide (inner.stacks 1 = inner.stacks 12)))
    (compiled_halt_trace ht (1 : Fin 13) 11)
  refine ⟨n + 1, ?_, ?_⟩
  · have hn' : n ≤ 11 * (a.stacks 1).length + 2 * (a.stacks 12).length + 19 := by
      simpa [inner, equalityStacks] using hn
    omega
  · simpa only [hin, hout, equality] using he

abbrev compareIndex : Cmd 8 32 :=
  .seq (.call (copyProgram 9 1 15 (0 : Fin 8) 1))
    (.seq (.call (copyProgram 16 12 15 (0 : Fin 8) 1))
      (.seq equality (RecordPrograms.atom (.pop 11 4 1))))

abbrev compared (a : Data) : Data :=
  ⟨Function.update
      (Function.update (fun j => if j.val < 5 then false else a.regs j) 1 true)
      4 (decide (a.stacks 9 = a.stacks 16)), a.stacks⟩

/-- Both unary words are copied before comparison; the original index words
and every surrounding stack survive the diagonal test. -/
theorem compareIndex_eval (a : Data) (h1 : a.stacks 1 = []) (h12 : a.stacks 12 = [])
    (h11 : a.stacks 11 = []) (h15 : a.stacks 15 = []) :
    ∃ n ≤ 18 * (a.stacks 9).length + 9 * (a.stacks 16).length + 31,
      Eval compareIndex n a (compared a) := by
  let a1 : Data := ⟨readRegs a.regs 0 1 none, copyStacks 9 1 a.stacks⟩
  let a2 : Data := ⟨readRegs a1.regs 0 1 none, copyStacks 16 12 a1.stacks⟩
  have hfirst := TupleProgram.copy_eval 9 1 15 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) a h15
  have hsecond := TupleProgram.copy_eval 16 12 15 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) a1
    (by simpa [a1, copyStacks] using h15)
  obtain ⟨ne, hne, he⟩ := equality_eval a2
  let a3 := afterEquality a2 (decide (a2.stacks 1 = a2.stacks 12))
  have hp : Eval (RecordPrograms.atom (.pop 11 4 1)) 1 a3 (compared a) := by
    have ht := Eval.base (StructuredProgram.Eval.atom
      (StructuredProgram.Atom.pop (11 : Fin 32) (4 : Fin 8) 1) a3)
    convert ht using 1
    apply congrArg₂ StructuredProgram.State.mk
    · have hl : a2.stacks 1 = a.stacks 9 := by simp [a2, a1, copyStacks, h1, h12]
      have hr : a2.stacks 12 = a.stacks 16 := by simp [a2, a1, copyStacks, h1, h12]
      have hz : a2.stacks 11 = [] := by simp [a2, a1, copyStacks, h11]
      have hanswer : a3.stacks 11 = [decide (a.stacks 9 = a.stacks 16)] := by
        change decide (a2.stacks 1 = a2.stacks 12) :: a2.stacks 11 = _
        rw [hl, hr, hz]
      have hregs : a3.regs = (fun j => if j.val < 5 then false else a.regs j) := by
        change (fun j => if j.val < 5 then false else a2.regs j) = _
        funext j
        by_cases hj : j.val < 5
        · simp [hj]
        · have hj0 : j ≠ 0 := by intro heq; subst j; norm_num at hj
          have hj1 : j ≠ 1 := by intro heq; subst j; norm_num at hj
          simp [hj, a2, a1, readRegs, hj0, hj1]
      change (compared a).regs = readRegs a3.regs 4 1 (a3.stacks 11).head?
      rw [hanswer, hregs]
      funext j
      by_cases hj1 : j = 1 <;> by_cases hj4 : j = 4 <;>
        simp_all [ readRegs, Function.update_apply]
    · funext j
      by_cases hj1 : j = 1 <;> by_cases hj12 : j = 12 <;> by_cases hj11 : j = 11 <;>
        simp_all [ a3, a2, a1, afterEquality, copyStacks,
          StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr
          ]
  refine ⟨7 * (a.stacks 9).length + 5 +
    (7 * (a1.stacks 16).length + 5 + (ne + 1)), ?_, ?_⟩
  · simp [a2, a1, copyStacks, h1, h12] at hne ⊢
    omega
  · exact hfirst.seq (hsecond.seq (he.seq hp))

def factor (differences negatives : List Word) (j : ℕ) : UniversalRowProgram.Factor Word :=
  ⟨differences.getD j [], negatives.getD j []⟩

def prependFactor (differences negatives : List Word) (j : ℕ) (out : Word) : Word :=
  true :: (Encoding.frame (UniversalRowProgram.encodeFactor (factor differences negatives j)) ++ out)

abbrev selected : Cmd 8 32 :=
  .seq UniversalRowFactors.readFactor UniversalRowFactors.emitFactor

theorem selected_eval (differences negatives : List Word) (width index : Word) (a : Data)
    (hd : a.stacks 0 = differences.flatten) (hn : a.stacks 26 = negatives.flatten)
    (hw : a.stacks 29 = width) (hi : a.stacks 9 = index)
    (hid : index.length < differences.length) (hin : index.length < negatives.length)
    (hds : ∀ row ∈ differences, row.length = width.length)
    (hns : ∀ row ∈ negatives, row.length = width.length)
    (h1 : a.stacks 1 = []) (h12 : a.stacks 12 = [])
    (h2 : a.stacks 2 = []) (h4 : a.stacks 4 = []) (h5 : a.stacks 5 = [])
    (h6 : a.stacks 6 = []) (h7 : a.stacks 7 = []) (h15 : a.stacks 15 = [])
    (h22 : a.stacks 22 = []) (h23 : a.stacks 23 = []) :
    ∃ b : Data,
      Eval selected (2 * index.length * (14 * width.length + 17) + 78 * width.length + 86) a b ∧
      b.stacks = Function.update a.stacks 21
        (prependFactor differences negatives index.length (a.stacks 21)) := by
  let mid : Data := ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks 1 (differences.getD index.length []))
      12 (negatives.getD index.length [])⟩
  have hr := UniversalRowFactors.readFactor_eval differences negatives width index a
    hd hn hw hi hid hin hds hns h1 h12 h2 h4 h5 h6 h7 h15
  obtain ⟨b, he, hb⟩ := UniversalRowFactors.emitFactor_eval mid
    (differences.getD index.length []) (negatives.getD index.length [])
    (by simp [mid]) (by simp [mid])
    (by simpa [mid] using h22) (by simpa [mid] using h23)
  refine ⟨b, ?_, ?_⟩
  · have hdl : (differences.getD index.length []).length = width.length := by
      rw [List.getD_eq_getElem _ _ hid]
      exact hds _ (List.getElem_mem hid)
    have hnl : (negatives.getD index.length []).length = width.length := by
      rw [List.getD_eq_getElem _ _ hin]
      exact hns _ (List.getElem_mem hin)
    have ht := hr.seq he
    convert ht using 1
    simp only [hdl, hnl]
    ring
  · rw [hb]
    funext j
    by_cases hj1 : j = 1 <;> by_cases hj12 : j = 12 <;> by_cases hj21 : j = 21 <;>
      simp_all [mid, prependFactor, factor, Function.update_apply]

structure Ready (differences negatives : List Word) (width outer : Word) (a : Data) : Prop where
  differences : a.stacks 0 = differences.flatten
  negatives : a.stacks 26 = negatives.flatten
  width : a.stacks 29 = width
  outer : a.stacks 16 = outer
  empty : ∀ j : Fin 32, j ∈ [1, 2, 4, 5, 6, 7, 11, 12, 15, 22, 23] → a.stacks j = []

abbrev resetFlags : Cmd 8 32 :=
  .seq (RecordPrograms.atom (.set 5 false))
    (.seq (RecordPrograms.atom (.set 6 true)) (RecordPrograms.atom (.set 7 false)))

abbrev resetState (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 5 false) 6 true) 7 false,
    a.stacks⟩

theorem resetFlags_eval (a : Data) : Eval resetFlags 3 a (resetState a) := by
  have h1 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (5 : Fin 8) false) a)
  have h2 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (6 : Fin 8) true)
    ((StructuredProgram.Atom.set (5 : Fin 8) false).eval a))
  have h3 := Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.set (7 : Fin 8) false)
    ((StructuredProgram.Atom.set (6 : Fin 8) true).eval
      ((StructuredProgram.Atom.set (5 : Fin 8) false).eval a)))
  exact h1.seq (h2.seq h3)

abbrev callback : Cmd 8 32 :=
  .seq compareIndex
    (.seq (.ite 4 (.base .skip) selected)
      (.seq (.call (clearProgram 9 (0 : Fin 8) 1)) resetFlags))

def updated (differences negatives : List Word) (outer index out : Word) : Word :=
  if index = outer then out else prependFactor differences negatives index.length out

def callbackCost (width outer : ℕ) (index : Word) : ℕ :=
  (28 * width + 60) * index.length + 9 * outer + 80 * width + 140

theorem callback_eval (differences negatives : List Word) (width outer index : Word) (a : Data)
    (ha : Ready differences negatives width outer a) (hi : a.stacks 9 = index)
    (hid : index.length < differences.length) (hin : index.length < negatives.length)
    (hds : ∀ row ∈ differences, row.length = width.length)
    (hns : ∀ row ∈ negatives, row.length = width.length) :
    ∃ n ≤ callbackCost width.length outer.length index, ∃ b : Data,
      Eval callback n a b ∧ b.regs 5 = false ∧ b.regs 6 = true ∧ b.regs 7 = false ∧
      b.stacks = Function.update (Function.update a.stacks 21
        (updated differences negatives outer index (a.stacks 21))) 9 [] := by
  obtain ⟨nc, hnc, hc⟩ := compareIndex_eval a (ha.empty 1 (by simp))
    (ha.empty 12 (by simp)) (ha.empty 11 (by simp)) (ha.empty 15 (by simp))
  let mid := compared a
  have hbranch : ∃ nb ≤ 2 * index.length * (14 * width.length + 17) + 78 * width.length + 87,
      ∃ b : Data, Eval (.ite 4 (.base .skip) selected) nb mid b ∧
        b.stacks = Function.update a.stacks 21
          (updated differences negatives outer index (a.stacks 21)) := by
    by_cases heq : index = outer
    · refine ⟨1, by omega, mid, ?_, ?_⟩
      · exact .ite_true (by simp [mid, hi, ha.outer, heq]) (.base (.skip _))
      · simp [mid, updated, heq]
    · obtain ⟨b, hb, hbs⟩ := selected_eval differences negatives width index mid
        ha.differences ha.negatives ha.width hi hid hin hds hns
        (ha.empty 1 (by simp)) (ha.empty 12 (by simp))
        (ha.empty 2 (by simp)) (ha.empty 4 (by simp)) (ha.empty 5 (by simp))
        (ha.empty 6 (by simp)) (ha.empty 7 (by simp)) (ha.empty 15 (by simp))
        (ha.empty 22 (by simp)) (ha.empty 23 (by simp))
      refine ⟨2 * index.length * (14 * width.length + 17) + 78 * width.length + 86 + 1,
        by omega, b,
        .ite_false (by simp [mid, hi, ha.outer, heq]) hb, ?_⟩
      simpa [mid, compared, updated, heq] using hbs
  obtain ⟨nb, hnb, b, hb, hbs⟩ := hbranch
  let cleared : Data := ⟨readRegs b.regs 0 1 none, clearStacks 9 b.stacks⟩
  have hclear := TupleProgram.clear_eval 9 (0 : Fin 8) 1 b
  have hreset := resetFlags_eval cleared
  refine ⟨nc + (nb + ((2 * (b.stacks 9).length + 3) + 3)), ?_, resetState cleared,
    hc.seq (hb.seq (hclear.seq hreset)), ?_, ?_, ?_, ?_⟩
  · have hb9 : b.stacks 9 = index := by simpa [hbs] using hi
    simp only [hi, ha.outer] at hnc
    rw [hb9]
    unfold callbackCost
    nlinarith
  · simp []
  · simp []
  · simp []
  · simp [ cleared, clearStacks, hbs]

def ports : RecordPrograms.Ports 8 32 where
  tag := 5
  present := 6
  found := 7
  source := 8
  payload := 9
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def invariant (differences negatives : List Word) (width outer : Word)
    (frame : Fin 32 → Word) (a : Data) : Prop :=
  Ready differences negatives width outer a ∧ ∀ j, j ≠ 21 → a.stacks j = frame j

def effect (differences negatives : List Word) (outer bits : Word) (a b : Data) : Prop :=
  b.stacks 21 = updated differences negatives outer bits.reverse (a.stacks 21)

theorem callback_contract (differences negatives : List Word) (width outer : Word)
    (frame : Fin 32 → Word)
    (hds : ∀ row ∈ differences, row.length = width.length)
    (hns : ∀ row ∈ negatives, row.length = width.length) :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false)
      (callbackCost width.length outer.length)
      (invariant differences negatives width outer frame)
      (effect differences negatives outer)
      (fun bits => bits.length < differences.length ∧ bits.length < negatives.length) := by
  intro bits tail base hvalid hbase
  let a := RecordPrograms.state ports base false true false tail bits.reverse
  have ha : Ready differences negatives width outer a := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [a, RecordPrograms.state, ports] using hbase.1.differences
    · simpa [a, RecordPrograms.state, ports] using hbase.1.negatives
    · simpa [a, RecordPrograms.state, ports] using hbase.1.width
    · simpa [a, RecordPrograms.state, ports] using hbase.1.outer
    · intro j hj
      have h := hbase.1.empty j hj
      fin_cases j <;> simp_all [a, RecordPrograms.state, ports]
  obtain ⟨n, hn, b, hb, h5, h6, h7, hbs⟩ := callback_eval
    differences negatives width outer bits.reverse a ha rfl
    (by simpa using hvalid.1) (by simpa using hvalid.2) hds hns
  let next : Data := ⟨b.regs, Function.update base.stacks 21 (b.stacks 21)⟩
  have hnext : invariant differences negatives width outer frame next := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa [next] using hbase.1.differences
    · simpa [next] using hbase.1.negatives
    · simpa [next] using hbase.1.width
    · simpa [next] using hbase.1.outer
    · intro j hj
      have h := hbase.1.empty j hj
      fin_cases j <;> simp_all [next]
    · intro j hj
      simpa [next, hj] using hbase.2 j hj
  have hend : b = RecordPrograms.state ports next false true false tail [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      fin_cases j <;> simp_all [ next, ports]
    · funext j
      rw [hbs]
      by_cases hj8 : j = 8 <;> by_cases hj9 : j = 9 <;> by_cases hj21 : j = 21 <;>
        simp_all [RecordPrograms.state, next, a, ports, Function.update_apply]
  refine ⟨n, next, ?_, hnext, ?_, ?_⟩
  · simpa [callbackCost] using hn
  · simp [effect, next, hbs, a, RecordPrograms.state, ports]
  · rw [← hend]
    exact hb

abbrev loop : Cmd 8 32 := RecordPrograms.iterate ports callback

def output (differences negatives : List Word) (outer : Word)
    (records : List Word) (acc : Word) : Word :=
  records.foldl (fun out bits => updated differences negatives outer bits.reverse out) acc

theorem unread_false (records : List Word) (suffix : Word) :
    RecordPrograms.unread (fun _ => false) records suffix = suffix := by
  induction records with
  | nil => rfl
  | cons bits rest ih => simpa [RecordPrograms.unread] using ih

theorem any_false {α : Type*} (xs : List α) : xs.any (fun _ => false) = false := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp

/-- Every record is parsed and processed by the fixed callback. The statement
records all preserved stacks, not only the emitted factor list. -/
theorem loop_eval (differences negatives : List Word) (width outer : Word)
    (records : List Word) (suffix : Word) (base : Data)
    (hbase : Ready differences negatives width outer base)
    (hds : ∀ row ∈ differences, row.length = width.length)
    (hns : ∀ row ∈ negatives, row.length = width.length)
    (hrecords : ∀ bits ∈ records,
      bits.length < differences.length ∧ bits.length < negatives.length)
    (v pr f : Bool) :
    ∃ n ≤ 3 + RecordPrograms.budget (callbackCost width.length outer.length) records,
      ∃ next : Data,
        Eval loop n
          (RecordPrograms.state ports base v pr f (Encoding.encodeList id records ++ suffix) [])
          (RecordPrograms.state ports next false true false suffix []) ∧
        Ready differences negatives width outer next ∧
        next.stacks 21 = output differences negatives outer records (base.stacks 21) ∧
        (∀ j, j ≠ 21 → next.stacks j = base.stacks j) := by
  obtain ⟨n, next, hn, hnext, hv, he⟩ := RecordPrograms.iterate_run_with_on ports callback
    (fun _ => false) (callbackCost width.length outer.length)
    (invariant differences negatives width outer base.stacks)
    (effect differences negatives outer)
    (fun bits => bits.length < differences.length ∧ bits.length < negatives.length)
    (callback_contract differences negatives width outer base.stacks hds hns)
    records suffix base hrecords ⟨hbase, by intros; rfl⟩ v pr f
  refine ⟨n, hn, next, ?_, hnext.1, ?_, hnext.2⟩
  · simpa [loop, unread_false, any_false] using he
  · exact hv.fold_of_false (by intros; rfl) (fun a => a.stacks 21)
      (fun out bits => updated differences negatives outer bits.reverse out)
      (by intros; assumption)

def indexWord (i : ℕ) : Word := List.replicate i true

@[simp] theorem indexWord_length (i : ℕ) : (indexWord i).length = i := by
  simp [indexWord]

@[simp] theorem indexWord_reverse (i : ℕ) : (indexWord i).reverse = indexWord i := by
  simp [indexWord]

@[simp] theorem indexWord_inj (i j : ℕ) : indexWord i = indexWord j ↔ i = j := by
  constructor
  · intro h
    simpa using congrArg List.length h
  · rintro rfl
    rfl

def factors (differences negatives : List Word) (i : ℕ) (positions : List ℕ) :
    List (UniversalRowProgram.Factor Word) :=
  (positions.filter fun j => decide (j ≠ i)).map (factor differences negatives)

theorem output_append (differences negatives : List Word) (outer : Word)
    (xs ys : List Word) (acc : Word) :
    output differences negatives outer (xs ++ ys) acc =
      output differences negatives outer ys (output differences negatives outer xs acc) := by
  simp [output, List.foldl_append]

/-- Descending traversal plus prepending restores the given ascending order.
The only discarded entry is the canonical unary word for the outer index. -/
theorem output_reverse_indices (differences negatives : List Word) (i : ℕ)
    (positions : List ℕ) (tail : List (UniversalRowProgram.Factor Word)) :
    output differences negatives (indexWord i) (positions.reverse.map indexWord)
        (Encoding.encodeList UniversalRowProgram.encodeFactor tail) =
      Encoding.encodeList UniversalRowProgram.encodeFactor
        (factors differences negatives i positions ++ tail) := by
  induction positions with
  | nil => simp [output, factors]
  | cons j rest ih =>
      rw [List.reverse_cons, List.map_append, output_append]
      change updated differences negatives (indexWord i) (indexWord j).reverse
        (output differences negatives (indexWord i) (rest.reverse.map indexWord)
          (Encoding.encodeList UniversalRowProgram.encodeFactor tail)) = _
      rw [ih]
      by_cases h : j = i <;>
        simp [updated, h, factors, prependFactor, Encoding.encodeList]

theorem loop_indices_eval (differences negatives : List Word) (width : Word) (i : ℕ)
    (positions : List ℕ) (suffix : Word) (base : Data)
    (hbase : Ready differences negatives width (indexWord i) base)
    (hacc : base.stacks 21 = [false])
    (hds : ∀ row ∈ differences, row.length = width.length)
    (hns : ∀ row ∈ negatives, row.length = width.length)
    (hpositions : ∀ j ∈ positions, j < differences.length ∧ j < negatives.length)
    (v pr f : Bool) :
    ∃ n ≤ 3 + RecordPrograms.budget (callbackCost width.length i)
        (positions.reverse.map indexWord), ∃ next : Data,
      Eval loop n
        (RecordPrograms.state ports base v pr f
          (Encoding.encodeList id (positions.reverse.map indexWord) ++ suffix) [])
        (RecordPrograms.state ports next false true false suffix []) ∧
      Ready differences negatives width (indexWord i) next ∧
      next.stacks 21 = Encoding.encodeList UniversalRowProgram.encodeFactor
        (factors differences negatives i positions) ∧
      (∀ j, j ≠ 21 → next.stacks j = base.stacks j) := by
  have hv : ∀ bits ∈ positions.reverse.map indexWord,
      bits.length < differences.length ∧ bits.length < negatives.length := by
    intro bits hb
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
    simpa using hpositions j (by simpa using hj)
  obtain ⟨n, hn, next, he, hr, ho, hf⟩ := loop_eval differences negatives width (indexWord i)
    (positions.reverse.map indexWord) suffix base hbase hds hns hv v pr f
  refine ⟨n, by simpa using hn, next, he, hr, ?_, hf⟩
  rw [ho, hacc]
  simpa [Encoding.encodeList] using output_reverse_indices differences negatives i positions []

end SubexponentialSAT.Subexp.UniversalRowFactorLoop

end OAI.Algorithms
