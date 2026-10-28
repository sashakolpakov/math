import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPrefixLoop
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPrefixGrouping

namespace OAI.Algorithms

/-! The closed physical prefix producer. Its inputs are the three original
encoded lists; no precomputed grouping is required. -/

namespace SubexponentialSAT.SubexpFactorPrefixProgram

open BitProgram StructuredCalls
open Subexp.FactorPacketCoordinates (Word Prefix originBytes taylorBytes)

attribute [local simp] Fin.coe_ofNat_eq_mod

def inputJobs (regs : Fin 8 → Bool) (jobs : List Job) : Data :=
  state regs {origins := originStream (jobPrefixes jobs), taylor := taylorStream (jobPrefixes jobs), scopes := scopeStream jobs}

def outputJobs (regs : Fin 8 → Bool) (jobs : List Job) : Data :=
  state regs {taylor := taylorStream (jobPrefixes jobs), scopes := scopeStream jobs, output := groupStream (jobs.map Prod.snd)}

def budget (jobs : List Job) : ℕ :=
  7 * (taylorStream (jobPrefixes jobs)).length + 7 * (scopeStream jobs).length +
    groupLoopBudget jobs + 10 * (groupStream (jobs.map Prod.snd).reverse).length + 25

theorem command_eval_jobs (jobs : List Job)
    (valid : ∀ job ∈ jobs, job.1.length = job.2.length) (regs : Fin 8 → Bool) :
    ∃ n ≤ budget jobs, ∃ rf, Eval command n (inputJobs regs jobs) (outputJobs rf jobs) := by
  let v0 : View := {origins := originStream (jobPrefixes jobs), taylor := taylorStream (jobPrefixes jobs), scopes := scopeStream jobs}
  let v1 := {v0 with todoTaylor := taylorStream (jobPrefixes jobs)}
  obtain ⟨d1,h1,hs1⟩ := copy_eval 1 4 (by decide) (by decide) (by decide) (state regs v0) rfl
  have hd1 : d1 = state d1.regs v1 := by
    apply SubexpScanPrimitives.state_ext <;> try rfl
    simpa [state, v1, v0, StackRoutines.copyStacks] using hs1
  rw [hd1] at h1
  let v2 := {v1 with todoScopes := scopeStream jobs}
  obtain ⟨d2,h2,hs2⟩ := copy_eval 2 5 (by decide) (by decide) (by decide) (state d1.regs v1) rfl
  have hd2 : d2 = state d2.regs v2 := by
    apply SubexpScanPrimitives.state_ext <;> try rfl
    simpa [state, v2, v1, v0, StackRoutines.copyStacks] using hs2
  rw [hd2] at h2
  let r3 := Function.update d2.regs (0 : Fin 8) false
  let v3 := {v2 with reverseGroups := [false]}
  have h3 : Eval (push 15 false) 2 (state d2.regs v2) (state r3 v3) := by
    simpa [state, v3, v2, v1, v0] using push_eval 15 false (state d2.regs v2)
  have hscope : scopeStream jobs = scopeFlag jobs :: scopeAfter jobs [] := by
    simpa using scopeStream_eq jobs []
  have h4 : Eval popScope 1 (state r3 v3) (readyGroups r3 v0 jobs [false] [false] [] [false]) := by
    simpa [popScope, state, readyGroups, between, v3, v2, v1, v0,
      chunk_encodeList, originStream, taylorStream, hscope] using pop_eval 5 7 6 (state r3 v3)
  obtain ⟨ng,hng,r5,h5⟩ := groupLoop_eval jobs valid r3 v0 [false] [false] [] [false]
  let v5 : View := {taylor := taylorStream (jobPrefixes jobs), scopes := scopeStream jobs, origins := [false], todoTaylor := [false], reverseGroups := groupStream (jobs.map Prod.snd).reverse}
  have h5' : Eval groupLoop ng (readyGroups r3 v0 jobs [false] [false] [] [false]) (state r5 v5) := by
    simpa [between, v5, v0, chunk_encodeList, groupStream] using h5
  let r6 := readRegs r5 0 1 none
  let v6 := {v5 with origins := []}
  have h6 : Eval (clear 0) 5 (state r5 v5) (state r6 v6) := by
    simpa [state, v6, v5] using clear_eval 0 (state r5 v5)
  let r7 := readRegs r6 0 1 none
  let v7 := {v6 with todoTaylor := []}
  have h7 : Eval (clear 4) 5 (state r6 v6) (state r7 v7) := by
    simpa [state, v7, v6, v5] using clear_eval 4 (state r6 v6)
  let r8 := Function.update r7 (0 : Fin 8) false
  let v8 := {v7 with output := [false]}
  have h8 : Eval (push 3 false) 2 (state r7 v7) (state r8 v8) := by
    simpa [state, v8, v7, v6, v5] using push_eval 3 false (state r7 v7)
  obtain ⟨nr,hnr,d9,h9,hs9⟩ := reverseAt_eval groupReversePorts (state r8 v8)
    ((jobs.map Prod.snd).reverse.map groupBytes) []
    (by
      change groupStream (jobs.map Prod.snd).reverse =
        Encoding.encodeList id ((jobs.map Prod.snd).reverse.map groupBytes)
      rw [encodeList_map]
      rfl) rfl rfl
  have hd9 : d9 = outputJobs d9.regs jobs := by
    apply SubexpScanPrimitives.state_ext <;> try rfl
    simpa [state, outputJobs, groupReversePorts, v8, v7, v6, v5,
      groupStream, encodeList_map] using hs9
  rw [hd9] at h9
  have hnr' : nr ≤ 10 * (groupStream (jobs.map Prod.snd).reverse).length := by
    simpa only [groupStream,encodeList_map,Function.id_comp] using hnr
  have hrun := h1.seq (h2.seq (h3.seq (h4.seq (h5'.seq (h6.seq (h7.seq (h8.seq h9)))))))
  refine ⟨_, ?_, d9.regs, hrun⟩
  simp only [state, store_taylor, store_scopes]
  dsimp [budget, v1, v0]
  omega

def inputState (regs : Fin 8 → Bool) (origins : List (List Word))
    (columns : List (List (List Word))) (scopes : List (List ℕ)) : Data :=
  state regs {origins := Encoding.encodeList (Encoding.encodeList id) origins, taylor := Encoding.encodeList (Encoding.encodeList (Encoding.encodeList id)) columns, scopes := Encoding.encodeList scopeBytes scopes}

def outputState (regs : Fin 8 → Bool) (origins : List (List Word))
    (columns : List (List (List Word))) (scopes : List (List ℕ)) : Data :=
  state regs {taylor := Encoding.encodeList (Encoding.encodeList (Encoding.encodeList id)) columns, scopes := Encoding.encodeList scopeBytes scopes, output := groupStream (grouped scopes origins columns)}

theorem zip_valid (scopes : List (List ℕ)) (groups : List (List Prefix))
    (h : groups.map List.length = scopes.map List.length) :
    ∀ job ∈ scopes.zip groups, job.1.length = job.2.length := by
  induction scopes generalizing groups with
  | nil => simp
  | cons s ss ih =>
    cases groups with
    | nil => simp at h
    | cons g gs =>
      simp only [List.map_cons, List.cons.injEq] at h
      intro job hj
      simp only [List.zip_cons_cons, List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact h.1.symm
      · exact ih gs h.2 job hj

theorem zip_projections (scopes : List (List ℕ)) (groups : List (List Prefix))
    (h : groups.map List.length = scopes.map List.length) :
    (scopes.zip groups).map Prod.fst = scopes ∧ (scopes.zip groups).map Prod.snd = groups := by
  have hl : scopes.length = groups.length := by
    have he := congrArg List.length h
    simpa only [List.length_map] using he.symm
  exact ⟨List.map_fst_zip hl.le, List.map_snd_zip hl.ge⟩

/-- The actual producer starts from the three flat lists. Its sole alignment
requirements count actual incidence records; scope contents may repeat and
scopes may be empty. -/
theorem command_eval (origins : List (List Word)) (columns : List (List (List Word)))
    (scopes : List (List ℕ)) (heq : origins.length = columns.length)
    (hsize : (scopes.map List.length).sum = origins.length) (regs : Fin 8 → Bool) :
    ∃ n ≤ budget (scopes.zip (grouped scopes origins columns)), ∃ rf,
      Eval command n (inputState regs origins columns scopes) (outputState rf origins columns scopes) := by
  let groups := grouped scopes origins columns
  have hl := grouped_lengths scopes origins columns heq hsize
  have hp := zip_projections scopes groups hl
  have hflat : jobPrefixes (scopes.zip groups) = zipPrefixes origins columns := by
    rw [jobPrefixes, List.flatMap_def, hp.2]
    exact grouped_flatten scopes origins columns heq hsize
  obtain ⟨n,hn,rf,hr⟩ := command_eval_jobs (scopes.zip groups) (zip_valid scopes groups hl) regs
  refine ⟨n,hn,rf,?_⟩
  simpa only [inputJobs, outputJobs, inputState, outputState, hflat, originStream_zip origins columns heq,
    taylorStream_zip origins columns heq, scopeStream, hp.1, hp.2] using hr

theorem program_trace (origins : List (List Word)) (columns : List (List (List Word)))
    (scopes : List (List ℕ)) (heq : origins.length = columns.length)
    (hsize : (scopes.map List.length).sum = origins.length) (regs : Fin 8 → Bool) :
    ∃ n ≤ budget (scopes.zip (grouped scopes origins columns)) + 1, ∃ rf,
      Trace program n ((inputState regs origins columns scopes).withPC (some program.entry))
        ((outputState rf origins columns scopes).withPC none) := by
  obtain ⟨n,hn,rf,hr⟩ := command_eval origins columns scopes heq hsize regs
  exact ⟨n+1, by omega, rf, compiled_halt_trace hr 0 3⟩

theorem primitive_execution (origins : List (List Word)) (columns : List (List (List Word)))
    (scopes : List (List ℕ)) (heq : origins.length = columns.length)
    (hsize : (scopes.map List.length).sum = origins.length) (regs : Fin 8 → Bool) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (budget (scopes.zip (grouped scopes origins columns)) + 1))
      (primitiveCfg program ((inputState regs origins columns scopes).withPC (some program.entry)))
      (primitiveCfg program ((outputState rf origins columns scopes).withPC none)) := by
  obtain ⟨n,hn,rf,hr⟩ := program_trace origins columns scopes heq hsize regs
  exact ⟨rf, BitProgram.primitive_execution program ⟨n,hn,hr⟩⟩

end SubexponentialSAT.SubexpFactorPrefixProgram

end OAI.Algorithms
