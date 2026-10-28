import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryExecution
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLocalBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighBranchSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramOuterCarriedMono

/-! Fixed finite syntax for both marked and final accepted queries. The only
program parameter is the fixed clause width. Every mark regenerates its own
physical high mask and zero counter. The semantic proof must establish that
the actual frontend guard holds on every reachable input. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram

open OAI BitProgram StructuredCalls HighQueryAdapter
noncomputable section

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

/-- Packing, searched ring production, interpolation and the denominator are
executed once per marked or accepted query, before high-assignment iteration. -/
def preparationProgram := compiled NativeQueryPreparation.command 700 728

def prepare : Code := .call (ProgramLinking.liftProgram preparationProgram
  id HighMarkedFrontend.stackMap)

/-- The stream already decodes the high context. Only the durable-counter copy
precedes it; the actual guard reset follows it even if the stream clobbers21. -/
def conditioned : Code := .seq copyHighCounter
  (.seq QueryStreamProgram.command restoreHighGuard)

/-- The real binary adder consumes each canonical residual count323 into788.
Neither a successful branch list nor a Boolean early exit is materialized. -/
def branch : Code := SqrtLog.LeafBranchProgram.body highPorts conditioned

def highLoop : Code := ExecCNFTupleEnumeration.enumerate highPorts.counter branch

/-- This initializer reads the current338 mask, including when it is empty.
The singleton zero tuple is still visited once in that case. -/
def seed : Code := .call HighCountSeed.initializeProgram

def preparedCount : Code := .seq prepare (.seq seed highLoop)

/-- The failed guard does no ring allocation. It clears the count word before
the common canonical return. Correctness on reachable inputs proves guard8 true;
this syntactic alternative is not used as a count-correctness argument. -/
def reject : Code := .call (StackRoutines.clearProgram 788 0 1)

def guardedCount : Code := .ite 8 preparedCount reject

/-- The marked frontend stages the actual current reference321 exactly once.
The complete canonical count is returned on323 for natural-number accumulation. -/
def marked (k : ℕ) : Code := .seq (HighMarkedFrontend.command k)
  (.seq guardedCount HighQueryExecution.markedReturn)

/-- The accepted frontend stages no mark. History-only source assembly is
performed by AcceptedQueryStage before this call, and788 is the full output. -/
def accepted (k : ℕ) : Code := .seq (HighMarkedFrontend.acceptedCommand k)
  (.seq guardedCount HighQueryExecution.acceptedReturn)

def markedProgram (k : ℕ) := compiled (marked k) 321 323
def acceptedProgram (k : ℕ) := compiled (accepted k) 700 788

/-- This measured physical composition is the branch syntax used by highLoop.
The supplied evaluation is specifically the fixed stream command, not a query
oracle or a callback chosen by the caller. -/
theorem conditioned_eval (a b : Data) (n : ℕ)
    (he : Eval QueryStreamProgram.command n (copiedHighCounter a) b) :
    Eval conditioned (copyHighCost a + (n + 1)) a
      ⟨Function.update b.regs 21 true,b.stacks⟩ :=
  (copyHighCounter_eval a).seq (he.seq (restoreHighGuard_eval b))

/-- Every successful generated query takes the physically tested true branch. -/
theorem guardedCount_true_eval (a b : Data) (n : ℕ)
    (hg : a.regs 8 = true) (he : Eval preparedCount n a b) :
    Eval guardedCount (n + 1) a b := .ite_true hg he

open HashGreedyProgram.NativeRound

private theorem restore_space (a : Data) (B : ℕ)
    (hB : ∀ i, (a.stacks i).length ≤ B) : StageSpace restoreHighGuard 1 a B := by
  constructor
  intro k z hk hz i
  have hc : k = 0 ∨ k = 1 := by omega
  rcases hc with rfl | rfl
  · cases hz
    exact hB i
  · rw [trace_same_length_unique hz (compiled_trace (restoreHighGuard_eval a) 778 777)]
    exact hB i

/-- Local composition around the fixed stream command preserves a uniform
prefix envelope; the exponential high-iteration count never enters it. -/
theorem conditioned_resources (a b : Data) (steps L D K : ℕ)
    (he : Eval QueryStreamProgram.command steps (copiedHighCounter a) b)
    (hs : StageSpace QueryStreamProgram.command steps (copiedHighCounter a) K)
    (hD : ∀ i, (a.stacks i).length ≤ D)
    (h330 : (a.stacks 330).length ≤ L) (h792 : (a.stacks 792).length ≤ L)
    (h789 : (a.stacks 789).length ≤ L) :
    Eval conditioned (copyHighCost a + (steps + 1)) a
      ⟨Function.update b.regs 21 true,b.stacks⟩ ∧
      copyHighCost a + (steps + 1) ≤ steps + 11 * L + 12 ∧
      StageSpace conditioned (copyHighCost a + (steps + 1) + 1) a (max D K) := by
  have hc : StageSpace copyHighCounter (copyHighCost a) a (max D K) := by
    constructor
    intro k z hk hz i
    exact (HighBranchSpace.copy_high_space a D hD k z hk hz i).trans (Nat.le_max_left _ _)
  have hq : StageSpace QueryStreamProgram.command steps (copiedHighCounter a) (max D K) :=
    ⟨fun k z hk hz i => (hs.bound k z hk hz i).trans (Nat.le_max_right _ _)⟩
  have hb : ∀ i, (b.stacks i).length ≤ max D K := by
    intro i
    exact hq.bound steps _ le_rfl (compiled_trace he 778 777) i
  have hr := restoreHighGuard_eval b
  have htail := StageSpace.seq he hr hq (restore_space b _ hb)
  have hwhole := StageSpace.seq (copyHighCounter_eval a) (he.seq hr) hc htail
  have hout := conditioned_eval a b steps he
  have htime := HighQueryLocalBounds.copy_cost_le a L h330 h792 h789
  exact ⟨hout,by omega,⟨StructuredSpace.compiled_halt_stack_bound hout 778 777 hwhole.bound⟩⟩

namespace Carried

open SqrtLog.ProgramTapeReplay

/-- Exactly the five words left unrestricted by the greedy query-time
quantifiers. Their bytes cannot affect this fixed query's control flow. -/
def words : Finset (Fin 896) := {320,322,770,771,781}

local notation "H" => (fun i : Fin 896 => i ∈ words)

private structure SafeAvoids (c : Cmd 40 896) : Prop where
  proof : AvoidsCmd H c

private theorem SafeAvoids.call {l : Nat} {p : Program 40 896 l}
    (hp : AvoidsProgram H p) :
    SafeAvoids (.call p) :=
  ⟨hp⟩

private structure LowerSafeAvoids (c : Cmd 40 768) : Prop where
  proof : AvoidsCmd (H ∘ HighMarkedFrontend.stackMap) c

private theorem LowerSafeAvoids.intro {c : Cmd 40 768}
    (hc : AvoidsCmd (H ∘ HighMarkedFrontend.stackMap) c) : LowerSafeAvoids c :=
  ⟨hc⟩

private theorem LowerSafeAvoids.ofMono {K : Fin 768 → Prop} {c : Cmd 40 768}
    (sub : ∀ i, (H ∘ HighMarkedFrontend.stackMap) i → K i)
    (hc : AvoidsCmd K c) : LowerSafeAvoids c :=
  ⟨avoidsCmd_mono sub hc⟩

private theorem LowerSafeAvoids.seq {first second : Cmd 40 768}
    (hfirst : LowerSafeAvoids first) (hsecond : LowerSafeAvoids second) :
    LowerSafeAvoids (.seq first second) :=
  ⟨⟨hfirst.proof, hsecond.proof⟩⟩

private theorem LowerSafeAvoids.liftCall {c : Cmd 40 768}
    (hc : LowerSafeAvoids c) (input output : Fin 768) :
    SafeAvoids (.call (ProgramLinking.liftProgram (compiled c input output)
      id HighMarkedFrontend.stackMap)) :=
  SafeAvoids.call (avoids_liftProgram H _ id HighMarkedFrontend.stackMap
    (avoids_compiled _ c hc.proof input output))

private theorem clear_bank {r s : ℕ} (K : Fin s → Prop)
    (tmp : Fin s) (value present : Fin r) (ports : List (Fin s))
    (ht : ¬K tmp) (hp : ∀ i∈ports, ¬K i) :
    AvoidsCmd K (BankRoutines.clearCmd tmp value present ports) := by
  induction ports with
  | nil => exact avoids_clearProgram K tmp value present ht
  | cons i is ih => exact ⟨avoids_clearProgram K i value present (hp i (by simp)),
      ih (fun j hj => hp j (by simp [hj]))⟩

private theorem lower_subset (i : Fin 768) (hi : H (HighMarkedFrontend.stackMap i)) :
    SqrtLog.LeafProgram.OuterCarried.hidden i := by
  simp only [words,Finset.mem_insert,Finset.mem_singleton,HighMarkedFrontend.stackMap,
    Fin.ext_iff,Fin.val_castAdd,Fin.coe_ofNat_eq_mod] at hi
  simp only [SqrtLog.LeafProgram.OuterCarried.hidden,List.mem_cons,
    Fin.ext_iff,Fin.coe_ofNat_eq_mod]
  have hv := i.isLt
  omega

private theorem mark_input :
    AvoidsCmd (H ∘ HighMarkedFrontend.stackMap) SqrtLog.LeafProgram.Query.markInput := by
  refine ⟨avoids_copyProgram _ 321 699 698 0 1 (by decide) (by decide) (by decide),
    avoids_transferProgram _ 699 705 0 1 (by decide) (by decide), ?_⟩
  exact ⟨True.intro,⟨by change ¬(H ∘ HighMarkedFrontend.stackMap) 706; decide,True.intro⟩⟩

private theorem no_mark_input :
    AvoidsCmd (H ∘ HighMarkedFrontend.stackMap) SqrtLog.LeafProgram.Query.noMarkInput :=
  ⟨True.intro,⟨by change ¬(H ∘ HighMarkedFrontend.stackMap) 705; decide,
    ⟨by change ¬(H ∘ HighMarkedFrontend.stackMap) 706; decide,True.intro⟩⟩⟩

theorem frontend (k : ℕ) : AvoidsCmd H (HighMarkedFrontend.command k) := by
  have hfront := LowerSafeAvoids.ofMono lower_subset
    (SqrtLog.LeafQueryFrontend.frontend_avoids_outerCarried k)
  have hmark := LowerSafeAvoids.intro mark_input
  let hs := (hmark.seq hfront).liftCall 321 338
  have hpack : ∃ c, c = HighMarkedFrontend.command k ∧ SafeAvoids c := by
    refine ⟨_, ?_, hs⟩
    rw [HighMarkedFrontend.command, HighMarkedFrontend.localProgram,
      SqrtLog.LeafProgram.Query.markedFrontend]
  obtain ⟨_, rfl, hc⟩ := hpack
  exact hc.proof

theorem accepted_frontend (k : ℕ) : AvoidsCmd H (HighMarkedFrontend.acceptedCommand k) := by
  have hfront := LowerSafeAvoids.ofMono lower_subset
    (SqrtLog.LeafQueryFrontend.frontend_avoids_outerCarried k)
  have hmark := LowerSafeAvoids.intro no_mark_input
  let hs := (hmark.seq hfront).liftCall 700 338
  have hpack : ∃ c, c = HighMarkedFrontend.acceptedCommand k ∧ SafeAvoids c := by
    refine ⟨_, ?_, hs⟩
    rw [HighMarkedFrontend.acceptedCommand, HighMarkedFrontend.acceptedLocalProgram,
      HighMarkedFrontend.acceptedLocalCommand]
  obtain ⟨_, rfl, hc⟩ := hpack
  exact hc.proof

private theorem seed_generator : AvoidsCmd H HighCountSeed.command := by
  refine ⟨⟨avoids_clearProgram H 791 0 1 (by decide),
    clear_bank H 791 0 1 _ (by decide) ?_⟩,
    avoids_copyProgram H 338 792 791 0 1 (by decide) (by decide) (by decide), ?_⟩
  · simp only [HighCountSeed.changed,List.mem_cons,List.not_mem_nil,or_false]
    rintro i (rfl|rfl|rfl) <;> decide
  · apply avoids_call_lift_of_range
    intro i
    fin_cases i <;> decide

private theorem seed_install : AvoidsCmd H HighCountInit.command := by
  refine ⟨⟨avoids_clearProgram H 792 0 1 (by decide),
    clear_bank H 792 0 1 _ (by decide) ?_⟩,
    avoids_copyProgram H 330 789 792 0 1 (by decide) (by decide) (by decide), True.intro⟩
  simp only [HighCountInit.changed,List.mem_cons,List.not_mem_nil,or_false]
  rintro i (rfl|rfl|rfl|rfl|rfl|rfl) <;> decide

private theorem seed_program : AvoidsProgram H HighCountSeed.initializeProgram := by
  apply avoids_compiled
  exact ⟨avoids_compiled H _ seed_generator 338 330,
    avoids_compiled H _ seed_install 330 788⟩

private theorem copy_high : AvoidsCmd H copyHighCounter :=
  ⟨avoids_clearProgram H 330 0 1 (by decide),
    avoids_clearProgram H 792 0 1 (by decide),
    avoids_copyProgram H 789 330 792 0 1 (by decide) (by decide) (by decide)⟩

private theorem canonical : AvoidsCmd H HighQueryExecution.canonicalize := by
  apply avoids_compiled
  refine ⟨⟨avoids_clearProgram H 793 0 1 (by decide),
    avoids_clearProgram H 794 0 1 (by decide)⟩,?_⟩
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> decide

private theorem route (src dst : Fin 896) (hs : ¬H src) (hd : ¬H dst) :
    AvoidsCmd H (SqrtLog.LeafOuterProgram.route (src,dst)) :=
  ⟨avoids_clearProgram H dst 0 1 hd,
    avoids_copyProgram H src dst 767 0 1 hs hd (by decide)⟩

private theorem finish : AvoidsCmd H HashMarkedQueryAdapter.finish := by
  refine ⟨route 788 323 (by decide) (by decide),
    clear_bank H 767 0 1 _ (by decide) ?_,?_⟩
  · simp only [HashMarkedQueryAdapter.cleanupPorts,List.mem_cons,List.not_mem_nil,or_false]
    rintro i (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> decide
  · exact ⟨True.intro,True.intro,True.intro,True.intro⟩

private theorem cleanup : AvoidsCmd H HighMarkedFrontend.cleanupCommand := by
  have hp : ∀ i∈SqrtLog.LeafProgram.Query.cleanupPorts,
      ¬(H ∘ HighMarkedFrontend.stackMap) i := by
    intro i hi hh
    have hprotect : SqrtLog.LeafProgram.Query.Protected i := by
      simp only [Function.comp_apply,words,Finset.mem_insert,Finset.mem_singleton,
        HighMarkedFrontend.stackMap,Fin.ext_iff,Fin.val_castAdd,Fin.coe_ofNat_eq_mod] at hh
      simp only [SqrtLog.LeafProgram.Query.Protected,Fin.ext_iff,Fin.coe_ofNat_eq_mod]
      have hv := i.isLt
      omega
    exact ((SqrtLog.LeafProgram.Query.mem_cleanupPorts i).mp hi).1 hprotect
  have hc : AvoidsCmd (H ∘ HighMarkedFrontend.stackMap) SqrtLog.LeafProgram.Query.cleanup := by
    unfold SqrtLog.LeafProgram.Query.cleanup
    generalize he : SqrtLog.LeafProgram.Query.cleanupPorts = ports
    have hv : ∀ i∈ports, ¬(H ∘ HighMarkedFrontend.stackMap) i := by
      rw [←he]
      exact hp
    exact ⟨avoids_clearProgram _ 699 0 1 (by decide),
      clear_bank (r:=40) (H ∘ HighMarkedFrontend.stackMap) 699 0 1 ports (by decide) hv⟩
  exact avoids_liftProgram H HighMarkedFrontend.cleanupLocalProgram id
    HighMarkedFrontend.stackMap
      (avoids_compiled _ SqrtLog.LeafProgram.Query.cleanup hc 699 323)

private theorem upper_cleanup : AvoidsCmd H HashMarkedReturn.upperClear := by
  have hp : ∀ i∈HashMarkedReturn.upperPorts, ¬H i := by
    intro i hi hh
    have hu := HashMarkedReturn.mem_upperPorts i |>.mp hi
    simp only [words,Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff,
      Fin.coe_ofNat_eq_mod] at hh
    omega
  unfold HashMarkedReturn.upperClear
  generalize he : HashMarkedReturn.upperPorts = ports
  have hv : ∀ i∈ports, ¬H i := by rw [←he]; exact hp
  exact clear_bank (r:=40) H 767 0 1 ports (by decide) hv

attribute [local irreducible] HashMarkedReturn.upperClear

private theorem sequence (first second : Code)
    (hf : AvoidsCmd H first) (hs : AvoidsCmd H second) :
    AvoidsCmd H (.seq first second) := ⟨hf,hs⟩

theorem marked_return : AvoidsCmd H HighQueryExecution.markedReturn := by
  have hupper : AvoidsCmd H HashMarkedReturn.upperClear := upper_cleanup
  have hlower : AvoidsCmd H HighMarkedFrontend.cleanupCommand := cleanup
  have hfinish : AvoidsCmd H HashMarkedQueryAdapter.finish := finish
  have hcanonical : AvoidsCmd H HighQueryExecution.canonicalize := canonical
  have hr : AvoidsCmd H HashMarkedQueryAdapter.resetParser :=
    ⟨True.intro,True.intro,True.intro,True.intro⟩
  unfold HighQueryExecution.markedReturn HashMarkedReturn.command
  generalize hu : HashMarkedReturn.upperClear = upper at hupper ⊢
  generalize hl : HighMarkedFrontend.cleanupCommand = lower at hlower ⊢
  generalize hf : HashMarkedQueryAdapter.finish = finishCommand at hfinish ⊢
  generalize hc : HighQueryExecution.canonicalize = canonicalCommand at hcanonical ⊢
  exact ⟨hcanonical,hfinish,hlower,hupper,hr⟩

theorem accepted_return : AvoidsCmd H HighQueryExecution.acceptedReturn := by
  have hi := sequence (SqrtLog.LeafOuterProgram.route (323,788))
    (.call (StackRoutines.clearProgram 323 0 1)) (route 323 788 (by decide) (by decide))
      (avoids_clearProgram H 323 0 1 (by decide))
  exact sequence HighQueryExecution.markedReturn HighQueryExecution.installAccepted marked_return hi

/-- The actual lower preparation excludes the collector tapes by its
instruction certificate; the selector words lie outside its lifted bank. -/
theorem preparation : AvoidsCmd H prepare := by
  have hcommand := LowerSafeAvoids.ofMono lower_subset
    NativeQueryPreparation.command_avoids
  let hs := hcommand.liftCall 700 728
  have hpack : ∃ c, c = prepare ∧ SafeAvoids c := by
    refine ⟨_, ?_, hs⟩
    rw [prepare, preparationProgram]
  obtain ⟨_, rfl, hc⟩ := hpack
  exact hc.proof

private theorem stream : AvoidsCmd H QueryStreamProgram.command := by
  apply avoidsCmd_mono (K:=fun i : Fin 896 => i.val=320 ∨ i.val=322 ∨
    i.val=770 ∨ i.val=771 ∨ i.val=781) _ QuerySelectorFrames.five_word_command_avoids
  intro i hi
  simpa only [words,Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff,
    Fin.coe_ofNat_eq_mod] using hi

theorem conditioned_avoids : AvoidsCmd H conditioned :=
  ⟨copy_high,stream,True.intro⟩

private theorem mass : AvoidsCmd H (SqrtLog.LeafProgram.Mass.invoke highPorts.mass) := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> decide

theorem branch_avoids : AvoidsCmd H branch := ⟨conditioned_avoids,mass⟩

private theorem increment :
    AvoidsCmd H (ExecCNFTupleEnumeration.incrementCmd highPorts.counter) := by
  apply avoids_call_lift_of_range
  intro i
  fin_cases i <;> decide

theorem high_loop : AvoidsCmd H highLoop :=
  ⟨True.intro,branch_avoids,increment,True.intro⟩

theorem prepared_count : AvoidsCmd H preparedCount :=
  ⟨preparation,seed_program,high_loop⟩

theorem guarded_count : AvoidsCmd H guardedCount :=
  ⟨prepared_count,avoids_clearProgram H 788 0 1 (by decide)⟩

/-- Both fixed complete query programs exclude all five caller words from
reads and writes, including every called table, presence test and cleanup. -/
theorem marked_avoids (k : ℕ) : AvoidsCmd H (marked k) :=
  ⟨frontend k,guarded_count,marked_return⟩

theorem accepted_avoids (k : ℕ) : AvoidsCmd H (accepted k) :=
  ⟨accepted_frontend k,guarded_count,accepted_return⟩

theorem marked_program_avoids (k : ℕ) : AvoidsProgram H (markedProgram k) :=
  avoids_compiled H _ (marked_avoids k) 321 323

theorem accepted_program_avoids (k : ℕ) : AvoidsProgram H (acceptedProgram k) :=
  avoids_compiled H _ (accepted_avoids k) 700 788

/-- Erasing the five carried words is proof-side only. The actual command
runs for exactly the same number of steps while retaining their full bytes. -/
theorem marked_shadow_eval (k : ℕ) {steps : ℕ} {a b : Data}
    (he : Eval (marked k) steps (rebaseState H (fun _ => []) a) b) :
    Eval (marked k) steps a (rebaseState H a.stacks b) :=
  CommandStackTransport.eval_shadow H (marked_avoids k) he

theorem accepted_shadow_eval (k : ℕ) {steps : ℕ} {a b : Data}
    (he : Eval (accepted k) steps (rebaseState H (fun _ => []) a) b) :
    Eval (accepted k) steps a (rebaseState H a.stacks b) :=
  CommandStackTransport.eval_shadow H (accepted_avoids k) he

/-- The same replay includes all prefix states through the final halt. Local
workspace and retained caller words contribute separate maximum bounds. -/
theorem marked_shadow_prefix (k : ℕ) {steps localBound frameBound : ℕ} {a b : Data}
    (he : Eval (marked k) steps (rebaseState H (fun _ => []) a) b)
    (hlocal : ∀ (p : ℕ) source, p ≤ steps + 1 → Trace (markedProgram k) p
      ((rebaseState H (fun _ => []) a).withPC (some (markedProgram k).entry)) source →
      ∀ i, ¬ H i → (source.stacks i).length ≤ localBound)
    (hframe : ∀ i, H i → (a.stacks i).length ≤ frameBound) :
    ∀ (p : ℕ) actual, p ≤ steps + 1 → Trace (markedProgram k) p
      (a.withPC (some (markedProgram k).entry)) actual →
      ∀ i, (actual.stacks i).length ≤ max localBound frameBound :=
  CommandStackTransport.eval_shadow_prefix_bound H (marked_avoids k) 321 323 he hlocal hframe

theorem accepted_shadow_prefix (k : ℕ) {steps localBound frameBound : ℕ} {a b : Data}
    (he : Eval (accepted k) steps (rebaseState H (fun _ => []) a) b)
    (hlocal : ∀ (p : ℕ) source, p ≤ steps + 1 → Trace (acceptedProgram k) p
      ((rebaseState H (fun _ => []) a).withPC (some (acceptedProgram k).entry)) source →
      ∀ i, ¬ H i → (source.stacks i).length ≤ localBound)
    (hframe : ∀ i, H i → (a.stacks i).length ≤ frameBound) :
    ∀ (p : ℕ) actual, p ≤ steps + 1 → Trace (acceptedProgram k) p
      (a.withPC (some (acceptedProgram k).entry)) actual →
      ∀ i, (actual.stacks i).length ≤ max localBound frameBound :=
  CommandStackTransport.eval_shadow_prefix_bound H (accepted_avoids k) 700 788 he hlocal hframe

/-- The canonical count words are visible outputs, unchanged by replay. -/
theorem marked_word (a b : Data) : (rebaseState H a.stacks b).stacks 323=b.stacks 323 := rfl

theorem accepted_word (a b : Data) : (rebaseState H a.stacks b).stacks 788=b.stacks 788 := rfl

end Carried

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram
