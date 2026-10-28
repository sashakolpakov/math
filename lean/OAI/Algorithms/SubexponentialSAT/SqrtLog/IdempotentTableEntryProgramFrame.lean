import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgramLookup

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

open BitProgram StructuredCalls SubexpScanPrimitives

def scanIRegs : Fin 4 → Fin 8 := ![0,1,3,4]
def scanJRegs : Fin 4 → Fin 8 := ![0,1,5,6]
def scanIPorts : Fin 2 → Fin 4 := ![0,3]
def scanJPorts : Fin 2 → Fin 4 := ![1,3]
def subRegs : Fin 4 → Fin 8 := ![0,1,2,7]
def subPorts : Fin 2 → Fin 4 := ![3,2]

abbrev scanI : Cmd 8 4 := .call (ProgramLinking.liftProgram scanProgram scanIRegs scanIPorts)
abbrev scanJ : Cmd 8 4 := .call (ProgramLinking.liftProgram scanProgram scanJRegs scanJPorts)
abbrev subtract : Cmd 8 4 := .call (ProgramLinking.liftProgram subtractProgram subRegs subPorts)

def afterI (r : Fin 8 → Bool) (i : ℕ) : Fin 8 → Bool :=
  ![false,false,r 2,decide (i%3=1),decide (i%3=2),r 5,r 6,r 7]
def afterJ (r : Fin 8 → Bool) (j : ℕ) : Fin 8 → Bool :=
  ![false,false,r 2,r 3,r 4,decide (j%3=1),decide (j%3=2),r 7]
def afterSub (r : Fin 8 → Bool) (rf : Fin 4 → Bool) : Fin 8 → Bool :=
  ![rf 0,rf 1,rf 2,r 3,r 4,r 5,r 6,rf 3]

theorem scanI_eval (i : ℕ) (r : Fin 8 → Bool) (ys zs bs : List Bool) :
    Eval scanI (10*(i/3)+2*(i%3)+5)
      (data r (List.replicate i true) ys zs bs)
      (data (afterI r i) [] ys zs (List.replicate (3*(i/3)) true ++ bs)) := by
  have hr : Function.Injective scanIRegs := by decide
  have hs : Function.Injective scanIPorts := by decide
  let d := data r (List.replicate i true) ys zs bs
  have hi : embedState scanIRegs scanIPorts d
      ⟨r ∘ scanIRegs,![List.replicate i true,bs]⟩ = d := by
    apply embedState_eq _ _ hr hs
    · intro x; rfl
    · intro x; fin_cases x <;> rfl
    · intros; rfl
    · intros; rfl
  have ho : embedState scanIRegs scanIPorts d
      ⟨remainderRegs (i%3),![[],List.replicate (3*(i/3)) true ++ bs]⟩ =
      data (afterI r i) [] ys zs (List.replicate (3*(i/3)) true ++ bs) := by
    apply embedState_eq _ _ hr hs
    · intro x; fin_cases x <;> rfl
    · intro x; fin_cases x <;> rfl
    · intro x hx; fin_cases x <;>
        simp_all [afterI,scanIRegs,Fin.exists_fin_succ,data,d]
    · intro x hx; fin_cases x <;>
        simp_all [scanIPorts,Fin.exists_fin_succ,data,d]
  have he := eval_call_lifted scanProgram scanIRegs scanIPorts d hr hs
    (a := ⟨r ∘ scanIRegs,![List.replicate i true,bs]⟩)
    (b := ⟨remainderRegs (i%3),![[],List.replicate (3*(i/3)) true ++ bs]⟩)
    (scan_trace i (r ∘ scanIRegs) bs)
  simpa only [hi,ho] using he

theorem scanJ_eval (j : ℕ) (r : Fin 8 → Bool) (xs zs bs : List Bool) :
    Eval scanJ (10*(j/3)+2*(j%3)+5)
      (data r xs (List.replicate j true) zs bs)
      (data (afterJ r j) xs [] zs (List.replicate (3*(j/3)) true ++ bs)) := by
  have hr : Function.Injective scanJRegs := by decide
  have hs : Function.Injective scanJPorts := by decide
  let d := data r xs (List.replicate j true) zs bs
  have hi : embedState scanJRegs scanJPorts d
      ⟨r ∘ scanJRegs,![List.replicate j true,bs]⟩ = d := by
    apply embedState_eq _ _ hr hs
    · intro x; rfl
    · intro x; fin_cases x <;> rfl
    · intros; rfl
    · intros; rfl
  have ho : embedState scanJRegs scanJPorts d
      ⟨remainderRegs (j%3),![[],List.replicate (3*(j/3)) true ++ bs]⟩ =
      data (afterJ r j) xs [] zs (List.replicate (3*(j/3)) true ++ bs) := by
    apply embedState_eq _ _ hr hs
    · intro x; fin_cases x <;> rfl
    · intro x; fin_cases x <;> rfl
    · intro x hx; fin_cases x <;>
        simp_all [afterJ,scanJRegs,Fin.exists_fin_succ,data,d]
    · intro x hx; fin_cases x <;>
        simp_all [scanJPorts,Fin.exists_fin_succ,data,d]
  have he := eval_call_lifted scanProgram scanJRegs scanJPorts d hr hs
    (a := ⟨r ∘ scanJRegs,![List.replicate j true,bs]⟩)
    (b := ⟨remainderRegs (j%3),![[],List.replicate (3*(j/3)) true ++ bs]⟩)
    (scan_trace j (r ∘ scanJRegs) bs)
  simpa only [hi,ho] using he

theorem subtract_eval (a b : ℕ) (r : Fin 8 → Bool) (xs ys : List Bool) :
    ∃ steps rf bs, steps ≤ 4*a+4 ∧
      Eval subtract steps
        (data r xs ys (List.replicate b true) (List.replicate a true))
        (data (afterSub r rf) xs ys (List.replicate (b-a) true) bs) ∧
      rf 3 = decide (b < a) ∧ bs.length ≤ a := by
  have hr : Function.Injective subRegs := by decide
  have hs : Function.Injective subPorts := by decide
  obtain ⟨steps,rf,bs,hcost,htrace,hflag,hbs⟩ := subtract_trace a b (r ∘ subRegs)
  let d := data r xs ys (List.replicate b true) (List.replicate a true)
  have hi : embedState subRegs subPorts d
      ⟨r ∘ subRegs,![List.replicate a true,List.replicate b true]⟩ = d := by
    apply embedState_eq _ _ hr hs
    · intro x; rfl
    · intro x; fin_cases x <;> rfl
    · intros; rfl
    · intros; rfl
  have ho : embedState subRegs subPorts d
      ⟨rf,![bs,List.replicate (b-a) true]⟩ =
      data (afterSub r rf) xs ys (List.replicate (b-a) true) bs := by
    apply embedState_eq _ _ hr hs
    · intro x; fin_cases x <;> rfl
    · intro x; fin_cases x <;> rfl
    · intro x hx; fin_cases x <;>
        simp_all [afterSub,subRegs,Fin.exists_fin_succ,data,d]
    · intro x hx; fin_cases x <;>
        simp_all [subPorts,Fin.exists_fin_succ,data,d]
  refine ⟨steps,rf,bs,hcost,?_,hflag,hbs⟩
  have he := eval_call_lifted subtractProgram subRegs subPorts d hr hs
    (a := ⟨r ∘ subRegs,![List.replicate a true,List.replicate b true]⟩)
    (b := ⟨rf,![bs,List.replicate (b-a) true]⟩) htrace
  simpa only [hi,ho] using he

end SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

end OAI.Algorithms
