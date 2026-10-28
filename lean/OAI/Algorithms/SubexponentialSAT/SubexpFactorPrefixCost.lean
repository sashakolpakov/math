import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPrefixProgram

namespace OAI.Algorithms

/-! The actual prefix-producer budget is linear in its encoded inputs. -/

namespace SubexponentialSAT.SubexpFactorPrefixProgram

open BitProgram StructuredCalls
open Subexp.FactorPacketCoordinates (Word Prefix originBytes taylorBytes prefixBytes)
open Subexp.FactorPacketRows (prefixStream)

def originMass (ps : List Prefix) : ℕ := (ps.map (fun p => (originBytes p).length)).sum
def taylorMass (ps : List Prefix) : ℕ := (ps.map (fun p => (taylorBytes p).length)).sum
def scopeMass (jobs : List Job) : ℕ := (jobs.map (fun j => (scopeBytes j.1).length)).sum

theorem encoded_length {α : Type*} (enc : α → Word) (xs : List α) :
    (Encoding.encodeList enc xs).length =
      2 * (xs.map (fun x => (enc x).length)).sum + 2 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [Encoding.encodeList, List.length_cons, List.length_append, Encoding.length_frame,
      ih, List.map_cons, List.sum_cons]
    omega

theorem encoded_reverse_length {α : Type*} (enc : α → Word) (xs : List α) :
    (Encoding.encodeList enc xs.reverse).length = (Encoding.encodeList enc xs).length := by
  simp [encoded_length, List.map_reverse]

@[simp] theorem originMass_append (xs ys : List Prefix) :
    originMass (xs ++ ys) = originMass xs + originMass ys := by
  simp [originMass]

@[simp] theorem taylorMass_append (xs ys : List Prefix) :
    taylorMass (xs ++ ys) = taylorMass xs + taylorMass ys := by
  simp [taylorMass]

theorem prefixStream_length (ps : List Prefix) :
    (prefixStream ps).length = 4 * (originMass ps + taylorMass ps) + 6 * ps.length + 1 := by
  induction ps with
  | nil => simp [prefixStream, Encoding.encodeList, originMass, taylorMass]
  | cons p ps ih =>
    simp only [prefixStream, Encoding.encodeList, List.length_cons, List.length_append,
      Encoding.length_frame, prefixBytes_eq] at *
    simp only [originMass, taylorMass, List.map_cons, List.sum_cons] at *
    omega

theorem pairsBudget_eq (ps : List Prefix) :
    pairsBudget ps = 33 * (originMass ps + taylorMass ps) + 60 * ps.length + 2 := by
  induction ps with
  | nil => simp [pairsBudget, pairLoopBudget, originMass, taylorMass]
  | cons p ps ih =>
    simp only [pairsBudget, pairLoopBudget, List.map_cons, List.sum_cons] at *
    simp only [pairCost, prefixBytes_eq, List.length_append, Encoding.length_frame,
      originMass, taylorMass, List.map_cons, List.sum_cons, List.length_cons] at *
    omega

theorem groupBytes_length (ps : List Prefix) :
    (groupBytes ps).length = 8 * (originMass ps + taylorMass ps) + 14 * ps.length + 4 := by
  simp only [groupBytes, List.length_append, Encoding.length_frame, List.length_replicate,
    prefixStream_length]
  omega

theorem groupStream_length (groups : List (List Prefix)) :
    (groupStream groups).length = 16 * (originMass groups.flatten + taylorMass groups.flatten) +
      28 * groups.flatten.length + 10 * groups.length + 1 := by
  induction groups with
  | nil => simp [groupStream, Encoding.encodeList, originMass, taylorMass]
  | cons ps groups ih =>
    simp only [groupStream, Encoding.encodeList, List.length_cons, List.length_append,
      Encoding.length_frame, groupBytes_length] at *
    simp only [List.flatten_cons, originMass_append, taylorMass_append, List.length_append]
    omega

theorem groupBudget_eq (scope : List ℕ) (ps : List Prefix) (h : scope.length = ps.length) :
    groupBudget scope ps = 169 * (originMass ps + taylorMass ps) +
      297 * ps.length + 11 * (scopeBytes scope).length + 97 := by
  have hc : SubexpSunflowerProgram.CountRecords.loopSteps (scope.map Encoding.encodeNat) =
      2 * (scopeBytes scope).length + 2 * scope.length + 3 := by
    have hl := encoded_length Encoding.encodeNat scope
    simp only [SubexpSunflowerProgram.CountRecords.loopSteps, List.map_map,
      Function.comp_def, List.length_map, scopeBytes]
    omega
  rw [groupBudget, hc, pairsBudget_eq, show (prefixStream ps.reverse).length = (prefixStream ps).length
    from encoded_reverse_length prefixBytes ps, prefixStream_length, groupBytes_length, h]
  omega

theorem groupLoopBudget_eq (jobs : List Job)
    (valid : ∀ job ∈ jobs, job.1.length = job.2.length) :
    groupLoopBudget jobs = 169 * (originMass (jobPrefixes jobs) + taylorMass (jobPrefixes jobs)) +
      297 * (jobPrefixes jobs).length + 11 * scopeMass jobs + 99 * jobs.length + 1 := by
  induction jobs with
  | nil => simp [groupLoopBudget, jobPrefixes, originMass, taylorMass, scopeMass]
  | cons j jobs ih =>
    have ht := ih (fun x hx => valid x (by simp [hx]))
    have hj := groupBudget_eq j.1 j.2 (valid j (by simp))
    simp only [groupLoopBudget, List.map_cons, List.sum_cons] at *
    simp only [jobPrefixes, List.flatMap_cons, originMass_append, taylorMass_append,
      List.length_append, scopeMass, List.map_cons, List.sum_cons, List.length_cons] at *
    omega

/-- The compiled halt is included. This bound charges actual copied and
parsed bits, rather than substituting a semantic list count for execution. -/
theorem budget_le_input (jobs : List Job)
    (valid : ∀ job ∈ jobs, job.1.length = job.2.length) :
    budget jobs + 1 ≤ 500 * ((originStream (jobPrefixes jobs)).length +
      (taylorStream (jobPrefixes jobs)).length + (scopeStream jobs).length + 1) := by
  have ho := encoded_length originBytes (jobPrefixes jobs)
  have ht := encoded_length taylorBytes (jobPrefixes jobs)
  have hs := encoded_length scopeBytes (jobs.map Prod.fst)
  have hg := groupStream_length (jobs.map Prod.snd)
  have hl := groupLoopBudget_eq jobs valid
  have hr : (groupStream (jobs.map Prod.snd).reverse).length =
      (groupStream (jobs.map Prod.snd)).length := encoded_reverse_length groupBytes _
  simp only [List.map_map, Function.comp_def, List.length_map] at hs
  change (scopeStream jobs).length = 2 * scopeMass jobs + 2 * jobs.length + 1 at hs
  change (originStream (jobPrefixes jobs)).length =
    2 * originMass (jobPrefixes jobs) + 2 * (jobPrefixes jobs).length + 1 at ho
  change (taylorStream (jobPrefixes jobs)).length =
    2 * taylorMass (jobPrefixes jobs) + 2 * (jobPrefixes jobs).length + 1 at ht
  change (groupStream (jobs.map Prod.snd)).length =
    16 * (originMass (jobPrefixes jobs) + taylorMass (jobPrefixes jobs)) +
      28 * (jobPrefixes jobs).length + 10 * (jobs.map Prod.snd).length + 1 at hg
  simp only [List.length_map] at hg
  unfold budget
  omega

def inputBytes (origins : List (List Word)) (columns : List (List (List Word)))
    (scopes : List (List ℕ)) : ℕ :=
  (Encoding.encodeList (Encoding.encodeList id) origins).length +
    (Encoding.encodeList (Encoding.encodeList (Encoding.encodeList id)) columns).length +
    (Encoding.encodeList scopeBytes scopes).length

theorem budget_grouped_le_input (origins : List (List Word))
    (columns : List (List (List Word))) (scopes : List (List ℕ))
    (heq : origins.length = columns.length)
    (hsize : (scopes.map List.length).sum = origins.length) :
    budget (scopes.zip (grouped scopes origins columns)) + 1 ≤
      500 * (inputBytes origins columns scopes + 1) := by
  let groups := grouped scopes origins columns
  have hl := grouped_lengths scopes origins columns heq hsize
  have hp := zip_projections scopes groups hl
  have hflat : jobPrefixes (scopes.zip groups) = zipPrefixes origins columns := by
    rw [jobPrefixes, List.flatMap_def, hp.2]
    exact grouped_flatten scopes origins columns heq hsize
  have hb := budget_le_input (scopes.zip groups) (zip_valid scopes groups hl)
  simpa only [inputBytes, hflat, originStream_zip origins columns heq,
    taylorStream_zip origins columns heq, scopeStream, hp.1] using hb

/-- This is the same actual program trace, now bounded by the byte lengths of
the three original encoded inputs. The program's final halt is included. -/
theorem program_trace_bounded (origins : List (List Word))
    (columns : List (List (List Word))) (scopes : List (List ℕ))
    (heq : origins.length = columns.length)
    (hsize : (scopes.map List.length).sum = origins.length) (regs : Fin 8 → Bool) :
    ∃ n ≤ 500 * (inputBytes origins columns scopes + 1), ∃ rf,
      Trace program n ((inputState regs origins columns scopes).withPC (some program.entry))
        ((outputState rf origins columns scopes).withPC none) := by
  obtain ⟨n, hn, rf, hr⟩ := program_trace origins columns scopes heq hsize regs
  exact ⟨n, hn.trans (budget_grouped_le_input origins columns scopes heq hsize), rf, hr⟩

theorem primitive_execution_bounded (origins : List (List Word))
    (columns : List (List (List Word))) (scopes : List (List ℕ))
    (heq : origins.length = columns.length)
    (hsize : (scopes.map List.length).sum = origins.length) (regs : Fin 8 → Bool) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (500 * (inputBytes origins columns scopes + 1)))
      (primitiveCfg program ((inputState regs origins columns scopes).withPC (some program.entry)))
      (primitiveCfg program ((outputState rf origins columns scopes).withPC none)) := by
  obtain ⟨n, hn, rf, hr⟩ := program_trace_bounded origins columns scopes heq hsize regs
  exact ⟨rf, BitProgram.primitive_execution program ⟨n, hn, hr⟩⟩

end SubexponentialSAT.SubexpFactorPrefixProgram

end OAI.Algorithms
