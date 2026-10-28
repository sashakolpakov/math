import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPrefixGroups

namespace OAI.Algorithms

/-! The physical outer factor loop, including empty scopes. -/

namespace SubexponentialSAT.SubexpFactorPrefixProgram

open BitProgram StructuredCalls
open Subexp.FactorPacketCoordinates (Word Prefix originBytes taylorBytes)

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Job := List ℕ × List Prefix
def jobPrefixes (jobs : List Job) : List Prefix := jobs.flatMap Prod.snd
def scopeStream (jobs : List Job) : Word := Encoding.encodeList scopeBytes (jobs.map Prod.fst)
def scopeFlag (jobs : List Job) : Bool := !jobs.isEmpty
def scopeAfter : List Job → Word → Word
  | [], suffix => suffix
  | job :: rest, suffix => Encoding.frame (scopeBytes job.1) ++ (scopeStream rest ++ suffix)

theorem scopeStream_eq (jobs : List Job) (suffix : Word) :
    scopeStream jobs ++ suffix = scopeFlag jobs :: scopeAfter jobs suffix := by
  cases jobs <;> simp [scopeStream, scopeFlag, scopeAfter, Encoding.encodeList, List.append_assoc]

def readyGroups (regs : Fin 8 → Bool) (v : View) (jobs : List Job) (ot tt suffix acc : Word) : Data :=
  state (readRegs regs 7 6 (some (scopeFlag jobs)))
    (between v (chunk originBytes (jobPrefixes jobs) ++ ot)
      (chunk taylorBytes (jobPrefixes jobs) ++ tt) (scopeAfter jobs suffix) acc)

def groupLoopBudget (jobs : List Job) : ℕ :=
  (jobs.map (fun job => groupBudget job.1 job.2 + 2)).sum + 1

theorem readyGroups_nil (regs : Fin 8 → Bool) (v : View) (ot tt suffix acc : Word) :
    (readyGroups regs v [] ot tt suffix acc).regs 7 = false := by
  simp [readyGroups, state, scopeFlag, readRegs]

theorem readyGroups_cons (regs : Fin 8 → Bool) (v : View) (job : Job)
    (jobs : List Job) (ot tt suffix acc : Word) :
    (readyGroups regs v (job :: jobs) ot tt suffix acc).regs 7 = true := by
  simp [readyGroups, state, scopeFlag, readRegs]

theorem groupLoop_eval (jobs : List Job)
    (valid : ∀ job ∈ jobs, job.1.length = job.2.length)
    (regs : Fin 8 → Bool) (v : View) (ot tt suffix acc : Word) :
    ∃ n ≤ groupLoopBudget jobs, ∃ rf, Eval groupLoop n
      (readyGroups regs v jobs ot tt suffix acc)
      (state rf (between v ot tt suffix (chunk groupBytes (jobs.map Prod.snd).reverse ++ acc))) := by
  induction jobs generalizing regs acc with
  | nil =>
    refine ⟨1, by simp [groupLoopBudget], (readyGroups regs v [] ot tt suffix acc).regs, ?_⟩
    simpa [groupLoop, readyGroups, jobPrefixes, scopeAfter, chunk, state, between] using
      (Eval.while_false (body := groupBody) (readyGroups_nil regs v ot tt suffix acc))
  | cons job jobs ih =>
    let r0 := (readyGroups regs v (job :: jobs) ot tt suffix acc).regs
    obtain ⟨ng,hng,rg,hg⟩ := groupStep_eval job.1 job.2 (valid job (by simp)) r0 v
      (chunk originBytes (jobPrefixes jobs) ++ ot) (chunk taylorBytes (jobPrefixes jobs) ++ tt)
      (scopeStream jobs ++ suffix) acc
    have hg' : Eval groupStep ng (readyGroups regs v (job :: jobs) ot tt suffix acc)
        (state rg (between v (chunk originBytes (jobPrefixes jobs) ++ ot)
          (chunk taylorBytes (jobPrefixes jobs) ++ tt) (scopeStream jobs ++ suffix)
          (true :: (Encoding.frame (groupBytes job.2) ++ acc)))) := by
      simpa [readyGroups, r0, state, scopeAfter, jobPrefixes, chunk_append,
        List.append_assoc] using hg
    have hp := pop_eval 5 7 6
      (state rg (between v (chunk originBytes (jobPrefixes jobs) ++ ot)
        (chunk taylorBytes (jobPrefixes jobs) ++ tt) (scopeStream jobs ++ suffix)
        (true :: (Encoding.frame (groupBytes job.2) ++ acc))))
    have hp' : Eval popScope 1
        (state rg (between v (chunk originBytes (jobPrefixes jobs) ++ ot)
          (chunk taylorBytes (jobPrefixes jobs) ++ tt) (scopeStream jobs ++ suffix)
          (true :: (Encoding.frame (groupBytes job.2) ++ acc))))
        (readyGroups rg v jobs ot tt suffix (true :: (Encoding.frame (groupBytes job.2) ++ acc))) := by
      simpa [popScope, state, between, readyGroups, scopeStream_eq] using hp
    obtain ⟨nr,hnr,rf,hr⟩ := ih (fun j hj => valid j (by simp [hj])) rg
      (true :: (Encoding.frame (groupBytes job.2) ++ acc))
    have hacc : chunk groupBytes (jobs.map Prod.snd).reverse ++
        (true :: (Encoding.frame (groupBytes job.2) ++ acc)) =
        chunk groupBytes ((job :: jobs).map Prod.snd).reverse ++ acc := by
      simp [List.reverse_cons, chunk_append, chunk, List.append_assoc]
    rw [hacc] at hr
    refine ⟨(ng + 1) + nr + 1, ?_, rf, ?_⟩
    · simp only [groupLoopBudget, List.map_cons, List.sum_cons] at *
      omega
    · exact Eval.while_true (readyGroups_cons regs v job jobs ot tt suffix acc) (hg'.seq hp') hr

end SubexponentialSAT.SubexpFactorPrefixProgram

end OAI.Algorithms
