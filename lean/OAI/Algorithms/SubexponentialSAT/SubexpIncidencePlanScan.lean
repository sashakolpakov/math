import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScopeMembershipProgram
import OAI.Algorithms.SubexponentialSAT.SubexpIncidencePlanPrimitives
import OAI.Algorithms.SubexponentialSAT.RecordMappedPrograms
import OAI.Algorithms.SubexponentialSAT.Subexp.IncidencePlanSpec

namespace OAI.Algorithms

/-! A fixed finite scan of encoded scopes. No slot map is supplied as input:
the local slot order is the encounter order of incident factors. -/
namespace SubexponentialSAT.SubexpIncidencePlanScan

open BitProgram StructuredCalls
open SubexpIncidencePlanPrimitives

abbrev Data := StructuredProgram.State 10 10
abbrev unary (n : ℕ) : List Bool := List.replicate n true
abbrev scopeBytes := Encoding.encodeList Encoding.encodeNat

def data (regs : Fin 10 → Bool) (v j : ℕ) (source output payload : List Bool)
    (degree : ℕ) : Data :=
  ⟨regs, ![[], [], (Encoding.encodeNat v).reverse, [], [], unary j,
    source, output, payload, unary degree]⟩

def pushIndex (j : ℕ) (out : List Bool) : List Bool :=
  true :: (Encoding.frame (unary j) ++ out)

def indexPrefix (js : List ℕ) : List Bool :=
  js.flatMap fun j => true :: Encoding.frame (unary j)

abbrev addDegree : Cmd 10 10 := .ite 4 (increment 9) (.base .skip)

def addedDegree (selected : Bool) (d : Data) : Data :=
  if selected then incremented 9 d else d

theorem addDegree_eval (d : Data) (selected : Bool) (h : d.regs 4 = selected) :
    Eval addDegree (if selected then 3 else 1) d (addedDegree selected d) := by
  cases selected
  · exact .ite_false h (.base (.skip d))
  · exact .ite_true h (increment_eval 9 d)

abbrev callback : Cmd 10 10 :=
  .seq SubexpScopeMembershipProgram.command
    (.seq addDegree (.seq (copy 5 1 3) (.seq emit (increment 5))))

def callbackBound (v j : ℕ) (scope : List ℕ) : ℕ :=
  128 * (v + 2) * ((scopeBytes scope).length + 1) + 16 * (j + 2)

theorem callback_eval (regs : Fin 10 → Bool) (v j degree : ℕ)
    (scope : List ℕ) (source out : List Bool) :
    ∃ (n : ℕ) (rf : Fin 10 → Bool),
      Eval callback n (data regs v j source out (scopeBytes scope).reverse degree)
        (data rf v (j + 1) source
          (if v ∈ scope then pushIndex j out else out) []
          (degree + if v ∈ scope then 1 else 0)) ∧
      (∀ i : Fin 10, 7 ≤ i.val → rf i = regs i) ∧ n ≤ callbackBound v j scope := by
  let a := data regs v j source out (scopeBytes scope).reverse degree
  obtain ⟨nm, rm, hm, hf, hr, hn⟩ := SubexpScopeMembershipProgram.scope_eval v scope a
    rfl rfl rfl rfl rfl rfl
  let b : Data := ⟨rm, Function.update a.stacks 8 []⟩
  let c := addedDegree (decide (v ∈ scope)) b
  let e := copied 5 1 c
  let f := emitted (decide (v ∈ scope)) (unary j) e
  let g := incremented 5 f
  have ha := addDegree_eval b (decide (v ∈ scope)) hf
  have hc : c.stacks 3 = [] := by
    by_cases hs : v ∈ scope <;> simp [c, addedDegree, incremented, b, a, data, hs]
  have he := copy_eval 5 1 3 c (by decide) (by decide) (by decide) hc
  have hep : e.stacks 1 = (unary j).reverse := by
    by_cases hs : v ∈ scope <;>
      simp [e, copied, StackRoutines.copyStacks, c, addedDegree, incremented, b, a, data, hs]
  have hef : e.regs 4 = decide (v ∈ scope) := by
    by_cases hs : v ∈ scope <;>
      simp [e, copied, readRegs, c, addedDegree, incremented, b, hs, hf]
  have hemit := emit_eval (decide (v ∈ scope)) (unary j) e hep hef
  have hinc := increment_eval 5 f
  have hend : g = data g.regs v (j + 1) source
      (if v ∈ scope then pushIndex j out else out) []
      (degree + if v ∈ scope then 1 else 0) := by
    apply congrArg (StructuredProgram.State.mk g.regs)
    funext i
    fin_cases i <;> by_cases hs : v ∈ scope <;>
      simp [ incremented, f, emitted, e, copied, StackRoutines.copyStacks,
        c, addedDegree, b, a, data, pushIndex, hs, List.replicate_succ]
  have hrun := hm.seq (ha.seq (he.seq (hemit.seq hinc)))
  change Eval callback _ a g at hrun
  rw [hend] at hrun
  refine ⟨_, g.regs, hrun, ?_, ?_⟩
  · intro i hi
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
    have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
    have hi4 : i ≠ 4 := by intro h; subst i; change 7 ≤ 4 at hi; omega
    by_cases hs : v ∈ scope <;>
      simpa [g, incremented, f, emitted, e, copied, readRegs, c, addedDegree,
        b, a, data, hi0, hi1, hi4, hs] using hr i hi
  · have h5 : (c.stacks 5).length = j := by
      by_cases hs : v ∈ scope <;>
        simp [c, addedDegree, incremented, b, a, data, hs]
    have hem := emit_cost (decide (v ∈ scope)) (unary j)
    simp only [List.length_replicate] at hem
    dsimp [callbackBound, scopeBytes] at *
    rw [h5]
    split <;> omega

def ports : RecordPrograms.Ports 10 10 where
  tag := 7
  present := 8
  found := 9
  source := 6
  payload := 8
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

abbrev command : Cmd 10 10 := RecordPrograms.iterate ports callback

def scanBudget (v : ℕ) : ℕ → List (List ℕ) → ℕ
  | _, [] => 0
  | j, C :: Cs => 6 * (scopeBytes C).length + callbackBound v j C + 7 +
      scanBudget v (j + 1) Cs

private theorem state_data (regs : Fin 10 → Bool) (v j degree : ℕ)
    (source out payload : List Bool) (t pr f : Bool) (src pay : List Bool) :
    RecordPrograms.state ports (data regs v j source out payload degree) t pr f src pay =
      data (Function.update (Function.update (Function.update regs 7 t) 8 pr) 9 f)
        v j src out pay degree := by
  apply congrArg (StructuredProgram.State.mk _)
  funext i
  fin_cases i <;> simp [ ports, data]

theorem loop_eval (scopes : List (List ℕ)) (regs : Fin 10 → Bool)
    (v j degree : ℕ) (out suffix : List Bool) :
    ∃ (n : ℕ) (rf : Fin 10 → Bool),
      Eval (RecordPrograms.loop ports callback) n
        (RecordMappedPrograms.afterTag ports scopeBytes (data regs v j [] out [] degree)
          scopes suffix)
        (data rf v (j + scopes.length) suffix
          (indexPrefix (Subexp.IncidencePlanSpec.incidenceFrom v j scopes).reverse ++ out) []
          (degree + (Subexp.IncidencePlanSpec.incidenceFrom v j scopes).length)) ∧
      rf 7 = false ∧ rf 8 = true ∧ rf 9 = false ∧ n ≤ 1 + scanBudget v j scopes := by
  induction scopes generalizing regs j degree out with
  | nil =>
      let rf := Function.update (Function.update (Function.update regs 7 false) 8 true) 9 false
      refine ⟨1, rf, ?_, by simp [rf], by simp [rf], by simp [rf], by simp [scanBudget]⟩
      have h : (RecordMappedPrograms.afterTag ports scopeBytes
          (data regs v j [] out [] degree) [] suffix) = data rf v j suffix out [] degree := by
        exact state_data regs v j degree [] out [] false true false suffix []
      rw [h]
      simpa [RecordPrograms.loop, Subexp.IncidencePlanSpec.incidenceFrom, indexPrefix] using
        (Eval.while_false (test := ports.tag) (body := RecordPrograms.body ports callback)
          (a := data rf v j suffix out [] degree) (by simp [data, rf, ports]))
  | cons C Cs ih =>
      let tail := Encoding.encodeList scopeBytes Cs ++ suffix
      let ra := Function.update (Function.update (Function.update regs 7 false) 8 true) 9 false
      obtain ⟨nc, rc, hcb, hcr, hcn⟩ := callback_eval ra v j degree C tail out
      have hreader := RecordPrograms.reader_eval ports (data regs v j [] out [] degree)
        (scopeBytes C) tail [] true true false
      have hin : RecordMappedPrograms.afterTag ports scopeBytes (data regs v j [] out [] degree)
          (C :: Cs) suffix = RecordPrograms.state ports (data regs v j [] out [] degree)
            true true false (Encoding.frame (scopeBytes C) ++ tail) [] := rfl
      rw [← hin] at hreader
      simp only [List.append_nil] at hreader
      rw [state_data] at hreader
      let out' := if v ∈ C then pushIndex j out else out
      let degree' := degree + if v ∈ C then 1 else 0
      have hrc7 : rc 7 = false := by simpa [ra] using hcr 7 (by decide)
      have hrc8 : rc 8 = true := by simpa [ra] using hcr 8 (by decide)
      have hrc9 : rc 9 = false := by simpa [ra] using hcr 9 (by decide)
      have hstate : RecordPrograms.state ports (data rc v (j+1) [] out' [] degree')
          false true false tail [] = data rc v (j+1) tail out' [] degree' := by
        rw [state_data]
        congr 1
        funext i
        fin_cases i <;> simp [hrc7, hrc8, hrc9]
      have hpop := RecordMappedPrograms.pop_list_eval ports scopeBytes
        (data rc v (j+1) [] out' [] degree') Cs suffix false true
      change Eval _ _ (RecordPrograms.state ports _ false true false tail []) _ at hpop
      rw [hstate] at hpop
      have hbranch := Eval.ite_false (yes := RecordPrograms.atom (.set ports.tag false))
        (show (data rc v (j+1) tail out' [] degree').regs ports.found = false from hrc9) hpop
      have hbody := hreader.seq (hcb.seq hbranch)
      obtain ⟨nr, rr, hrest, hr7, hr8, hr9, hrn⟩ := ih rc (j+1) degree' out'
      have hg : (RecordMappedPrograms.afterTag ports scopeBytes
          (data regs v j [] out [] degree) (C::Cs) suffix).regs ports.tag = true := by
        simp [RecordMappedPrograms.afterTag]
      have hrun := Eval.while_true hg hbody hrest
      refine ⟨6 * (scopeBytes C).length + 4 + (nc + (1 + 1)) + nr + 1,
        rr, ?_, hr7, hr8, hr9, ?_⟩
      · by_cases hs : v ∈ C <;>
          simpa [RecordPrograms.loop, RecordPrograms.body,
            Subexp.IncidencePlanSpec.incidenceFrom, hs, out', degree', indexPrefix,
            pushIndex, List.reverse_cons, List.flatMap_append, List.append_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrun
      · simp only [scanBudget]
        omega

theorem command_eval (scopes : List (List ℕ)) (regs : Fin 10 → Bool)
    (v j degree : ℕ) (out suffix : List Bool) :
    ∃ (n : ℕ) (rf : Fin 10 → Bool),
      Eval command n
        (data regs v j (Encoding.encodeList scopeBytes scopes ++ suffix) out [] degree)
        (data rf v (j + scopes.length) suffix
          (indexPrefix (Subexp.IncidencePlanSpec.incidenceFrom v j scopes).reverse ++ out) []
          (degree + (Subexp.IncidencePlanSpec.incidenceFrom v j scopes).length)) ∧
      rf 7 = false ∧ rf 8 = true ∧ rf 9 = false ∧ n ≤ 3 + scanBudget v j scopes := by
  obtain ⟨n, rf, hl, h7, h8, h9, hn⟩ := loop_eval scopes regs v j degree out suffix
  have hs := RecordPrograms.set_found_eval ports (data regs v j [] out [] degree)
    (regs 7) (regs 8) (regs 9) false (Encoding.encodeList scopeBytes scopes ++ suffix) []
  have hp := RecordMappedPrograms.pop_list_eval ports scopeBytes (data regs v j [] out [] degree)
    scopes suffix (regs 7) (regs 8)
  have hrun := hs.seq (hp.seq hl)
  have hstart : RecordPrograms.state ports (data regs v j [] out [] degree)
      (regs 7) (regs 8) (regs 9) (Encoding.encodeList scopeBytes scopes ++ suffix) [] =
      data regs v j (Encoding.encodeList scopeBytes scopes ++ suffix) out [] degree := by
    rw [state_data]
    simp only [Function.update_eq_self]
  rw [hstart] at hrun
  exact ⟨1+(1+n), rf, hrun, h7, h8, h9, by omega⟩

/-- The actual scan cost is polynomial in the encoded pattern and unary query. -/
theorem scanBudget_le (v j : ℕ) (scopes : List (List ℕ)) :
    scanBudget v j scopes ≤
      (128*(v+2)+16*(j+scopes.length+2)+20) *
        (Encoding.encodeList scopeBytes scopes).length := by
  induction scopes generalizing j with
  | nil => simp [scanBudget]
  | cons C Cs ih =>
      have h := ih (j+1)
      simp only [scanBudget,callbackBound,Encoding.length_encodeList_cons,List.length_cons]
      nlinarith

theorem incidenceFrom_length_le (v j : ℕ) (scopes : List (List ℕ)) :
    (Subexp.IncidencePlanSpec.incidenceFrom v j scopes).length ≤ scopes.length := by
  induction scopes generalizing j with
  | nil => rfl
  | cons C Cs ih =>
      have h := ih (j+1)
      by_cases hm : v ∈ C <;>
        simp [Subexp.IncidencePlanSpec.incidenceFrom,hm] <;> omega

theorem indexPrefix_length_le (js : List ℕ) (E : ℕ) (h : ∀ j ∈ js, j < E) :
    (indexPrefix js).length ≤ js.length*(2*E+2) := by
  induction js with
  | nil => simp [indexPrefix]
  | cons j js ih =>
      have hj := h j (by simp)
      have ht := ih (fun k hk => h k (by simp [hk]))
      simp [indexPrefix,Encoding.length_frame] at ht ⊢
      nlinarith

end SubexponentialSAT.SubexpIncidencePlanScan

end OAI.Algorithms
