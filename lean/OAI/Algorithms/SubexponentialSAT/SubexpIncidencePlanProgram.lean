import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpIncidencePlanScan
import OAI.Algorithms.SubexponentialSAT.SubexpIncidencePlanFinish
import OAI.Algorithms.SubexponentialSAT.SubexpUnaryRangeProgram

namespace OAI.Algorithms

/-!
# Encoded scopes to a concrete incidence read plan

This is one fixed finite program. Runtime stacks supply the encoded scope list,
the vertex token, and unary D and Delta. No slot assignment is supplied to the
machine. Incident slots are allocated in outer-list encounter order.
-/
namespace SubexponentialSAT.SubexpIncidencePlanProgram

open BitProgram StructuredCalls

abbrev Data := State 10 16
abbrev Code := Cmd 10 16
abbrev unary (n : ℕ) := List.replicate n true

def low : Fin 10 → Fin 16 := Fin.castAdd 6
theorem low_injective : Function.Injective low := by
  intro a b h
  exact Fin.ext (congrArg (fun x : Fin 16 => x.val) h)

def extend (d : State 10 10) (D Δ : ℕ) : Data :=
  ⟨d.regs, ![d.stacks 0,d.stacks 1,d.stacks 2,d.stacks 3,d.stacks 4,
    d.stacks 5,d.stacks 6,d.stacks 7,d.stacks 8,d.stacks 9,unary D,unary Δ,[],[],[],[]]⟩

theorem extend_stacks_eq (d : State 10 10) (D Δ : ℕ) (i : Fin 16) :
    (extend d D Δ).stacks i =
      if h : i.val < 10 then d.stacks ⟨i.val,h⟩
      else if i = 10 then unary D else if i = 11 then unary Δ else [] := by
  fin_cases i <;> rfl

theorem embed_low (base d : State 10 10) (D Δ : ℕ) :
    embedState id low (extend base D Δ) d = extend d D Δ := by
  apply embedState_eq_of_ports id low (extend base D Δ) (extend d D Δ) d
    Function.injective_id low_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have hn : ¬ i.val < 10 := by
      intro h
      exact hi ⟨⟨i.val,h⟩,Fin.ext rfl⟩
    simp only [extend_stacks_eq,dite_eq_right hn]

def scan : Code := .call (ProgramLinking.liftProgram
  (compiled SubexpIncidencePlanScan.command 6 7) id low)

def input (regs : Fin 10 → Bool) (D Δ v : ℕ) (scopes : List (List ℕ)) : Data :=
  extend (SubexpIncidencePlanScan.data regs v 0
    (Encoding.encodeList SubexpIncidencePlanScan.scopeBytes scopes) [] [] 0) D Δ

def incidencePrefix (v : ℕ) (scopes : List (List ℕ)) : List Bool :=
  SubexpIncidencePlanScan.indexPrefix
    (Subexp.IncidencePlanSpec.incidentIndices scopes v).reverse

theorem scan_eval (regs : Fin 10 → Bool) (D Δ v : ℕ) (scopes : List (List ℕ)) :
    ∃ (n : ℕ) (rf : Fin 10 → Bool), Eval scan n (input regs D Δ v scopes)
      (SubexpIncidencePlanFinish.state rf v scopes.length
        (Subexp.IncidencePlanSpec.degree scopes v) D Δ (incidencePrefix v scopes)) ∧
      n ≤ 4 + SubexpIncidencePlanScan.scanBudget v 0 scopes := by
  obtain ⟨n,rf,h,_,_,_,hn⟩ := SubexpIncidencePlanScan.command_eval scopes regs v 0 0 [] []
  have ht := compiled_halt_trace h 6 7
  have hl := eval_call_lifted (compiled SubexpIncidencePlanScan.command 6 7) id low
    (input regs D Δ v scopes) Function.injective_id low_injective ht
  unfold input at hl ⊢
  rw [embed_low,embed_low] at hl
  refine ⟨n+1,rf,?_,by omega⟩
  simpa [scan,Subexp.IncidencePlanSpec.degree,Subexp.IncidencePlanSpec.incidentIndices,
    SubexpIncidencePlanFinish.state,incidencePrefix,extend,SubexpIncidencePlanScan.data] using hl

def rangeMap : Fin 10 → Fin 16 := ![4,0,2,3,6,1,14,7,8,9]
theorem rangeMap_injective : Function.Injective rangeMap := by decide
def range : Code := .call (ProgramLinking.liftProgram SubexpUnaryRangeProgram.program id rangeMap)

theorem finish_stacks_eq (regs : Fin 10 → Bool) (v E degree D Δ : ℕ)
    (out index fuel : List Bool) (i : Fin 16) :
    (SubexpIncidencePlanFinish.state regs v E degree D Δ out index (unary v) fuel).stacks i =
      if i = 1 then index else if i = 7 then out else if i = 14 then fuel else
        (SubexpIncidencePlanFinish.state (fun _ => false) v E degree D Δ [] [] (unary v)).stacks i := by
  fin_cases i <;> rfl

theorem range_eval (regs : Fin 10 → Bool) (v E degree D Δ start count : ℕ) (out : List Bool) :
    ∃ rf, Eval range (SubexpUnaryRangeProgram.steps start count+2)
      (SubexpIncidencePlanFinish.state regs v E degree D Δ out (unary start) (unary v) (unary count))
      (SubexpIncidencePlanFinish.state rf v E degree D Δ
        (SubexpUnaryRangeProgram.indexPrefix (List.range' start count).reverse ++ out)
        (unary (start+count)) (unary v)) := by
  let a := SubexpIncidencePlanFinish.state regs v E degree D Δ out
    (unary start) (unary v) (unary count)
  let base : State 10 10 := ⟨regs,a.stacks ∘ rangeMap⟩
  obtain ⟨rf,ht⟩ := SubexpUnaryRangeProgram.program_trace base regs start count out
  have ha : embedState id rangeMap a (SubexpUnaryRangeProgram.data base regs start count out) = a := by
    apply embedState_eq_of_ports id rangeMap a a _ Function.injective_id rangeMap_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hb : embedState id rangeMap a
      (SubexpUnaryRangeProgram.data base rf (start+count) 0
        (SubexpUnaryRangeProgram.indexPrefix (List.range' start count).reverse ++ out)) =
      SubexpIncidencePlanFinish.state rf v E degree D Δ
        (SubexpUnaryRangeProgram.indexPrefix (List.range' start count).reverse ++ out)
        (unary (start+count)) (unary v) := by
    apply embedState_eq_of_ports id rangeMap a _ _ Function.injective_id rangeMap_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h1 : i ≠ 1 := fun h => hi ⟨5,h.symm⟩
      have h7 : i ≠ 7 := fun h => hi ⟨7,h.symm⟩
      have h14 : i ≠ 14 := fun h => hi ⟨6,h.symm⟩
      dsimp only [a]
      conv_lhs => rw [finish_stacks_eq]
      conv_rhs => rw [finish_stacks_eq]
      simp only [ite_eq_right h1,ite_eq_right h7,ite_eq_right h14]
  have h := eval_call_lifted SubexpUnaryRangeProgram.program id rangeMap a
    Function.injective_id rangeMap_injective ht
  rw [ha,hb] at h
  exact ⟨rf,h⟩

def command : Code := .seq scan (.seq SubexpIncidencePlanFinish.header
  (.seq SubexpIncidencePlanFinish.prepare range))

def bound (D Δ v : ℕ) (scopes : List (List ℕ)) : ℕ :=
  let E := scopes.length
  let d := Subexp.IncidencePlanSpec.degree scopes v
  4 + SubexpIncidencePlanScan.scanBudget v 0 scopes +
    (19*v+12*E+6*(incidencePrefix v scopes).length+44) +
    (7*Δ+20*d+7*D+7*E+14*v+7*v*Δ+41) +
    (SubexpUnaryRangeProgram.steps (SubexpIncidencePlanFinish.paddingStart v E d D Δ) (Δ-d)+2)

theorem encode_indexPrefix (js : List ℕ) :
    SubexpIncidencePlanScan.indexPrefix js ++ [false] =
      ProgramEncoding.encodeRecords (js.map unary) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
      simp [SubexpIncidencePlanScan.indexPrefix,ProgramEncoding.encodeRecords,Encoding.encodeList,
        List.append_assoc] at ih ⊢
      exact ih

theorem output_identity (D Δ v : ℕ) (scopes : List (List ℕ)) :
    SubexpUnaryRangeProgram.indexPrefix
      (List.range' (SubexpIncidencePlanFinish.paddingStart v scopes.length
        (Subexp.IncidencePlanSpec.degree scopes v) D Δ)
        (Δ-Subexp.IncidencePlanSpec.degree scopes v)).reverse ++
      SubexpIncidencePlanFinish.headerWord scopes.length v (incidencePrefix v scopes) =
    ProgramEncoding.encodeRecords
      ((Subexp.IncidencePlanSpec.producedPlan D Δ scopes v).map unary) := by
  rw [← encode_indexPrefix]
  simp [Subexp.IncidencePlanSpec.producedPlan,Subexp.IncidencePlanSpec.vertexPlan,
    SubexpIncidencePlanFinish.paddingStart,SubexpIncidencePlanFinish.headerWord,
    incidencePrefix,SubexpUnaryRangeProgram.indexPrefix,SubexpIncidencePlanScan.indexPrefix,
    List.flatMap_append,List.append_assoc]

/-- An actual execution computes the entire reversed unary read plan from
encoded scopes. The sole structural premise is the degree bound for padding. -/
theorem command_eval (regs : Fin 10 → Bool) (D Δ v : ℕ) (scopes : List (List ℕ))
    (hd : Subexp.IncidencePlanSpec.degree scopes v ≤ Δ) :
    ∃ (n : ℕ) (rf : Fin 10 → Bool), Eval command n (input regs D Δ v scopes)
      (SubexpIncidencePlanFinish.state rf v scopes.length
        (Subexp.IncidencePlanSpec.degree scopes v) D Δ
        (ProgramEncoding.encodeRecords ((Subexp.IncidencePlanSpec.producedPlan D Δ scopes v).map unary))
        (unary (scopes.length+D+v*Δ+Δ)) (unary v)) ∧ n ≤ bound D Δ v scopes := by
  obtain ⟨ns,rs,hs,hns⟩ := scan_eval regs D Δ v scopes
  obtain ⟨rh,hh⟩ := SubexpIncidencePlanFinish.header_eval rs v scopes.length
    (Subexp.IncidencePlanSpec.degree scopes v) D Δ (incidencePrefix v scopes)
  obtain ⟨rp,hp⟩ := SubexpIncidencePlanFinish.prepare_eval rh v scopes.length
    (Subexp.IncidencePlanSpec.degree scopes v) D Δ
    (SubexpIncidencePlanFinish.headerWord scopes.length v (incidencePrefix v scopes)) hd
  obtain ⟨rf,hr⟩ := range_eval rp v scopes.length (Subexp.IncidencePlanSpec.degree scopes v) D Δ
    (SubexpIncidencePlanFinish.paddingStart v scopes.length (Subexp.IncidencePlanSpec.degree scopes v) D Δ)
    (Δ-Subexp.IncidencePlanSpec.degree scopes v)
    (SubexpIncidencePlanFinish.headerWord scopes.length v (incidencePrefix v scopes))
  rw [output_identity] at hr
  have he : SubexpIncidencePlanFinish.paddingStart v scopes.length
      (Subexp.IncidencePlanSpec.degree scopes v) D Δ +
      (Δ-Subexp.IncidencePlanSpec.degree scopes v) = scopes.length+D+v*Δ+Δ := by
    unfold SubexpIncidencePlanFinish.paddingStart
    omega
  rw [he] at hr
  exact ⟨_,rf,hs.seq (hh.seq (hp.seq hr)),by dsimp [bound]; omega⟩

abbrev program : Program 10 16 (size command+1) := compiled command 6 7

theorem program_trace (regs : Fin 10 → Bool) (D Δ v : ℕ) (scopes : List (List ℕ))
    (hd : Subexp.IncidencePlanSpec.degree scopes v ≤ Δ) :
    ∃ (n : ℕ) (rf : Fin 10 → Bool), n ≤ bound D Δ v scopes+1 ∧
      Trace program n ((input regs D Δ v scopes).withPC (some program.entry))
        ((SubexpIncidencePlanFinish.state rf v scopes.length
          (Subexp.IncidencePlanSpec.degree scopes v) D Δ
          (ProgramEncoding.encodeRecords ((Subexp.IncidencePlanSpec.producedPlan D Δ scopes v).map unary))
          (unary (scopes.length+D+v*Δ+Δ)) (unary v)).withPC none) := by
  obtain ⟨n,rf,h,hn⟩ := command_eval regs D Δ v scopes hd
  exact ⟨n+1,rf,by omega,compiled_halt_trace h 6 7⟩

theorem program_primitive (regs : Fin 10 → Bool) (D Δ v : ℕ) (scopes : List (List ℕ))
    (hd : Subexp.IncidencePlanSpec.degree scopes v ≤ Δ) :
    ∃ rf, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program*(bound D Δ v scopes+1))
      (BitProgram.primitiveCfg program ((input regs D Δ v scopes).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((SubexpIncidencePlanFinish.state rf v scopes.length
          (Subexp.IncidencePlanSpec.degree scopes v) D Δ
          (ProgramEncoding.encodeRecords ((Subexp.IncidencePlanSpec.producedPlan D Δ scopes v).map unary))
          (unary (scopes.length+D+v*Δ+Δ)) (unary v)).withPC none)) := by
  obtain ⟨n,rf,h,hn⟩ := command_eval regs D Δ v scopes hd
  refine ⟨rf,?_⟩
  exact (StructuredCalls.primitive_execution h 6 7).mono
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right hn 1))

/-- The bytes produced by the machine are exactly the typed read-plan bytes
for the explicit occurrence-rank slot assignment. -/
theorem produced_records_eq_readPlan (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ) (v : Fin D) :
    ProgramEncoding.encodeRecords ((Subexp.IncidencePlanSpec.producedPlan D Δ scopes v.val).map unary) =
      ProgramEncoding.encodeRecords (Subexp.ReadPlan.unaryPlan
        (Subexp.ReadPlan.vertexPlan (Subexp.IncidencePlanSpec.pattern D scopes)
          (Subexp.IncidencePlanSpec.slots D Δ scopes hd) (List.finRange D)
          (List.finRange scopes.length) v).reverse) := by
  rw [Subexp.IncidencePlanSpec.producedPlan_eq_readPlan_reverse D Δ scopes hd v]
  rfl

end SubexponentialSAT.SubexpIncidencePlanProgram

end OAI.Algorithms
