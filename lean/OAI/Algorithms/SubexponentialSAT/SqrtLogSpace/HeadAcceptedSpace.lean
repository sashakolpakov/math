import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQuerySpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly

/-! Prefix bounds for the concrete accepted-head assignment path. Every local
physical cap is independent of the retained caller envelope. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace

open BitProgram StructuredCalls HighQueryAdapter

/-- The paid overlay has its proved sharp bound for any derivation of its
actual evaluation, so it composes directly inside the accepted branch. -/
theorem overlay_prefix {a b : State 40 896} {steps localCap bound : ℕ}
    (he : Eval NativeOverlay.prepare steps a b)
    (hh : (a.stacks 859).length =
      OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.highCount (a.stacks 670))
    (hm : (a.stacks 670).length = (a.stacks 869).length)
    (hmask : (a.stacks 670).length ≤ localCap)
    (hu : (a.stacks 870).length ≤ localCap) (hv : (a.stacks 871).length ≤ localCap)
    (hlocal : 66 * localCap + 42 ≤ bound)
    (hb : ∀ i, (a.stacks i).length ≤ bound) :
    ∀ q z, q ≤ steps → Trace (compiled NativeOverlay.prepare 860 860) q
      (a.withPC (some (compiled NativeOverlay.prepare 860 860).entry)) z →
      ∀ i, (z.stacks i).length ≤ bound := by
  obtain ⟨nt, rf, ht, _, hspace⟩ := HighQuerySpace.overlay_trace_space a localCap bound
    hh hm hmask hu hv hlocal hb
  have heq : steps + 1 = nt := StreamResources.halted_trace_steps_eq
    (compiled_halt_trace he 859 145) ht (by rfl) (by rfl)
  intro q z hq hz
  exact hspace q z (by omega) hz

/-- The actual overlay preserves all head-loop controller words, while its
ambient assignment word has exactly the retained mask length. -/
theorem overlay_frame {a b : State 40 896} {steps : ℕ}
    (he : Eval NativeOverlay.prepare steps a b)
    (hh : (a.stacks 859).length =
      OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.highCount (a.stacks 670))
    (hm : (a.stacks 670).length = (a.stacks 869).length) :
    b.stacks 859 = a.stacks 859 ∧ b.stacks 860 = a.stacks 860 ∧
      b.stacks 861 = a.stacks 861 ∧ (b.stacks 145).length = (a.stacks 670).length := by
  have hbits := NativeOverlay.reset_frame a 859 (by decide)
  have hmask := NativeOverlay.reset_frame a 670 (by decide)
  have hbase := NativeOverlay.reset_frame a 869 (by decide)
  obtain ⟨rf, hc⟩ := NativeOverlay.command_eval (NativeOverlay.resetState a)
    (fun i hi => BankRoutines.clearBankStacks_mem i NativeOverlay.changed a.stacks hi)
    (by simpa only [hbits, hmask] using hh) (by simpa only [hmask, hbase] using hm)
  have heq := Eval.final_unique (859 : Fin 896) he ((NativeOverlay.reset_eval a).seq hc)
  rw [heq]
  exact ⟨NativeOverlay.prepared_frame a rf 859 (by decide),
    NativeOverlay.prepared_frame a rf 860 (by decide),
    NativeOverlay.prepared_frame a rf 861 (by decide),
    NativeOverlay.prepared_length a rf hh⟩

open CounterPrograms CounterForPrograms

/-- Entry cleanup, every head assignment, and controller reclamation all
share one source trace and one unchanged caller envelope. The complete cost
includes both cleanup phases and has a fixed polynomial factor times `2^h`. -/
theorem head_resources (accepted : HeadSumProgram.Code)
    (I : ℕ → HeadSumProgram.Data → Prop)
    (h bound cost : ℕ)
    (hcursorI : ∀ i d, I i d → HeadSumProgram.Cursor h i d)
    (hbound : ∀ i d, I i d → ∀ j, (d.stacks j).length ≤ bound)
    (hbudget : 9 * (h + 1) + 8 ≤ bound)
    (spec : ∀ i d, I i d → d.stacks 861 = [] → 0 < value (d.stacks 860) →
      ∃ nb e, nb ≤ cost ∧ Eval (HeadSumProgram.body accepted) nb d e ∧
        e.stacks 860 = d.stacks 860 ∧ e.stacks 861 = [] ∧
        I (i + 1) (nextState HeadSumProgram.fuelPorts e))
    (hcallback : ∀ i d e nb, I i d → d.stacks 861 = [] →
      0 < value (d.stacks 860) → Eval (HeadSumProgram.body accepted) nb d e →
      ∀ q z, q ≤ nb → Trace (compiled (HeadSumProgram.body accepted) 860 860) q
        (d.withPC (some (compiled (HeadSumProgram.body accepted) 860 860).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound)
    (a : HeadSumProgram.Data) (hshape : a.stacks 651 = List.replicate h false)
    (hframe : ∀ j, (a.stacks j).length ≤ bound)
    (hi : I 0 (testResult HeadSumProgram.fuelPorts (HeadSumProgram.seeded (HeadSumAssembly.cleared a)))) :
    ∃ steps e,
      Trace (HeadSumAssembly.headProgram accepted) steps
        (a.withPC (some (HeadSumAssembly.headProgram accepted).entry))
        ((HeadSumProgram.finalized e).withPC none) ∧
      Eval (HeadSumAssembly.head accepted) (steps - 1) a (HeadSumProgram.finalized e) ∧
      I (2 ^ h) e ∧
      (HeadSumProgram.finalized e).stacks 853 = e.stacks 853 ∧
      (HeadSumProgram.finalized e).stacks 859 = [] ∧
      (HeadSumProgram.finalized e).stacks 860 = [] ∧
      (HeadSumProgram.finalized e).stacks 861 = [] ∧
      steps ≤ (2 * cost + 126 * bound + 54 * h + 286) * 2 ^ h ∧
      ∀ q z, q ≤ steps → Trace (HeadSumAssembly.headProgram accepted) q
        (a.withPC (some (HeadSumAssembly.headProgram accepted).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound := by
  have hclear := HeadSumAssembly.clearWork_eval a
  have hclearPrefix := HeadSumAssembly.clearWork_prefix hclear hframe
  have hcleared := hclearPrefix _ _ le_rfl (compiled_trace hclear 860 860)
  have hshape' : (HeadSumAssembly.cleared a).stacks 651 = List.replicate h false := by
    rw [HeadSumAssembly.cleared_frame a 651 (by decide) (by decide)]
    exact hshape
  have hcursor' : (HeadSumAssembly.cleared a).stacks 859 = [] :=
    HeadSumAssembly.cleared_controller a 859 (by decide)
  have hfuel' : (HeadSumAssembly.cleared a).stacks 860 = [] :=
    HeadSumAssembly.cleared_controller a 860 (by decide)
  have hscratch' : (HeadSumAssembly.cleared a).stacks 861 = [] :=
    HeadSumAssembly.cleared_controller a 861 (by decide)
  have htemp' : (HeadSumAssembly.cleared a).stacks 31 = [] :=
    HeadSumAssembly.cleared_low a 31
  obtain ⟨ns, e, hs, hI, hout, h859, h860, h861, htime, hspace⟩ :=
    HeadSumSpace.scan_resources accepted I h bound cost hcursorI hbound hbudget spec
      hcallback (HeadSumAssembly.cleared a) hshape' hcursor' hfuel' hscratch' htemp'
      hcleared hi
  have hcall : Eval (.call (HeadSumProgram.scanProgram accepted)) ns
      (HeadSumAssembly.cleared a) (HeadSumProgram.finalized e) := Eval.call _ hs
  have hcallPrefix : ∀ q z, q ≤ ns →
      Trace (compiled (.call (HeadSumProgram.scanProgram accepted)) 860 860) q
        ((HeadSumAssembly.cleared a).withPC
          (some (compiled (.call (HeadSumProgram.scanProgram accepted)) 860 860).entry)) z →
      ∀ j, (z.stacks j).length ≤ bound :=
    StructuredSpace.call_stack_bound _ _ _ _
      (compiled_site (.call (HeadSumProgram.scanProgram accepted)) 860 860) hs hspace
  have hwhole := hclear.seq hcall
  have hfull := StructuredSpace.sequence_stack_bound hclear hcall 860 860
    hclearPrefix hcallPrefix (HeadSumAssembly.headProgram accepted)
    (siteAddress (HeadSumAssembly.head accepted)) (exitAddress (HeadSumAssembly.head accepted))
    (compiled_site (HeadSumAssembly.head accepted) 651 853)
  have hscanTime := htime.trans (HeadSumSpace.scan_budget_le h bound cost)
  have hentryTime := HeadSumAssembly.clearWorkCost_le a bound hframe
  have hp : 1 ≤ 2 ^ h := Nat.one_le_pow _ _ (by decide)
  have hentryMul : 124 * bound + 190 ≤ (124 * bound + 190) * 2 ^ h := by
    nlinarith
  refine ⟨_, e, compiled_halt_trace hwhole 651 853, ?_, hI, hout, h859, h860, h861, ?_, ?_⟩
  · simpa only [HeadSumAssembly.head, Nat.add_sub_cancel] using hwhole
  · nlinarith
  · exact StructuredSpace.compiled_halt_stack_bound hwhole 651 853 hfull

/-- A single polynomial-time assignment evaluation may charge its bounded
boundary data once. The budget must be discharged by that actual local run;
this estimate is not applied to the exponential head loop. -/
theorem bounded_local_prefix (command : Cmd 40 896) (a : State 40 896)
    {steps inputCap budget bound : ℕ} (htime : steps ≤ budget)
    (hinput : ∀ i, (a.stacks i).length ≤ inputCap)
    (hlocal : 896 * inputCap + budget ≤ bound) :
    ∀ q z, q ≤ steps → Trace (compiled command 860 860) q
      (a.withPC (some (compiled command 860 860).entry)) z →
      ∀ i, (z.stacks i).length ≤ bound := by
  have hin : dataBits (a.withPC (some (compiled command 860 860).entry)) ≤ 896 * inputCap :=
    StreamResources.dataBits_le_mul _ hinput
  intro q z hq hz i
  exact (StructuredSpace.local_stack_bound (compiled command 860 860)
    (steps := budget) hin q z (hq.trans htime) hz i).trans hlocal

/-- The overlay returns to the compact semantic boundary cap, independently
of its larger transient envelope. This cap feeds the polynomial factor run. -/
theorem overlay_return_bound {a b : State 40 896} {steps inputCap : ℕ}
    (he : Eval NativeOverlay.prepare steps a b)
    (hh : (a.stacks 859).length =
      OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction.highCount (a.stacks 670))
    (hm : (a.stacks 670).length = (a.stacks 869).length)
    (hinput : ∀ i, (a.stacks i).length ≤ inputCap) :
    ∀ i, (b.stacks i).length ≤ inputCap := by
  have hbits := NativeOverlay.reset_frame a 859 (by decide)
  have hmask := NativeOverlay.reset_frame a 670 (by decide)
  have hbase := NativeOverlay.reset_frame a 869 (by decide)
  obtain ⟨rf, hc⟩ := NativeOverlay.command_eval (NativeOverlay.resetState a)
    (fun i hi => BankRoutines.clearBankStacks_mem i NativeOverlay.changed a.stacks hi)
    (by simpa only [hbits, hmask] using hh) (by simpa only [hmask, hbase] using hm)
  have heq := Eval.final_unique (859 : Fin 896) he ((NativeOverlay.reset_eval a).seq hc)
  rw [heq]
  exact NativeOverlay.prepared_bound a rf inputCap hh hinput

open OAI BitProgram StructuredCalls SqrtLog SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadSumProgram

/-- Normalization returns a compact dictionary and the paid reset clears its
workspace. Thus repeated accepted assignments retain the same semantic cap. -/
theorem accumulate_return_bound (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J steps inputCap : ℕ}
    (source seed : List (Product.Entry n (baseWidth p t) d))
    (hsource : Good ∅ u J source) (hseed : Good ∅ u J seed)
    (a e : HeadSumProgram.Data) (width degree zero table uCap zCap : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hlow : ∀ i : Fin 56, a.stacks (Fin.castAdd 840 i) =
      Product.tapes (Product.idle M.bits width zero table degree uCap zCap) i)
    (hseedWord : a.stacks 853 = Product.bytes seed)
    (hsourceWord : a.stacks 854 = Product.bytes source)
    (hs0 : a.stacks 883 = []) (hs1 : a.stacks 884 = [])
    (harray : u * J * (2 * (u + J + n) + 2 * (d * baseWidth p t) + 2) ≤ inputCap)
    (hinput : ∀ i, (a.stacks i).length ≤ inputCap)
    (he : Eval accumulate steps a e) :
    ∀ i, (e.stacks i).length ≤ inputCap := by
  obtain ⟨nt, b, _, hb, hg, hstacks, _, _⟩ := accumulate_eval p t M cache
    source seed hsource hseed a width degree zero table uCap zCap hd hw hlow
    hseedWord hsourceWord hs0 hs1
  have heq := Eval.final_unique (853 : Fin 896) he hb
  subst e
  have hbytes := (empty_bytes_length_le hg).trans harray
  intro i
  rw [hstacks]
  by_cases h854 : i = 854
  · subst i; simp
  by_cases h853 : i = 853
  · subst i; simpa using hbytes
  simp only [Function.update_of_ne h854, Function.update_of_ne h853,
    FactorEnvironment.reset_stacks]
  split
  · simp
  · exact hinput i

/-- A polynomial local body can be charged from its compact semantic boundary.
This discharges the resource callback for the whole exponential scan without
using its accumulated runtime in the space bound. -/
theorem head_resources_of_local_time (accepted : HeadSumProgram.Code)
    (I : ℕ → HeadSumProgram.Data → Prop)
    (h inputCap bound cost : ℕ)
    (hcursorI : ∀ i d, I i d → HeadSumProgram.Cursor h i d)
    (hcompact : ∀ i d, I i d → ∀ j, (d.stacks j).length ≤ inputCap)
    (hlocal : 896 * inputCap + cost ≤ bound)
    (hbudget : 9 * (h + 1) + 8 ≤ bound)
    (spec : ∀ i d, I i d → d.stacks 861 = [] → 0 < value (d.stacks 860) →
      ∃ nb e, nb ≤ cost ∧ Eval (HeadSumProgram.body accepted) nb d e ∧
        e.stacks 860 = d.stacks 860 ∧ e.stacks 861 = [] ∧
        I (i + 1) (nextState HeadSumProgram.fuelPorts e))
    (a : HeadSumProgram.Data) (hshape : a.stacks 651 = List.replicate h false)
    (hframe : ∀ j, (a.stacks j).length ≤ bound)
    (hi : I 0 (testResult HeadSumProgram.fuelPorts
      (HeadSumProgram.seeded (HeadSumAssembly.cleared a)))) :
    ∃ steps e,
      Trace (HeadSumAssembly.headProgram accepted) steps
        (a.withPC (some (HeadSumAssembly.headProgram accepted).entry))
        ((HeadSumProgram.finalized e).withPC none) ∧
      Eval (HeadSumAssembly.head accepted) (steps - 1) a (HeadSumProgram.finalized e) ∧
      I (2 ^ h) e ∧
      (HeadSumProgram.finalized e).stacks 853 = e.stacks 853 ∧
      (HeadSumProgram.finalized e).stacks 859 = [] ∧
      (HeadSumProgram.finalized e).stacks 860 = [] ∧
      (HeadSumProgram.finalized e).stacks 861 = [] ∧
      steps ≤ (2 * cost + 126 * bound + 54 * h + 286) * 2 ^ h ∧
      ∀ q z, q ≤ steps → Trace (HeadSumAssembly.headProgram accepted) q
        (a.withPC (some (HeadSumAssembly.headProgram accepted).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound := by
  have hcap : inputCap ≤ bound := by omega
  apply head_resources accepted I h bound cost hcursorI
    (fun i d hd j => (hcompact i d hd j).trans hcap) hbudget spec
    ?_ a hshape hframe hi
  intro i d e nb hI hs hf he
  obtain ⟨nb', e', ht, he', _, _, _⟩ := spec i d hI hs hf
  have hn := StreamResources.eval_steps_eq (860 : Fin 896) 860 he he'
  exact bounded_local_prefix (HeadSumProgram.body accepted) d
    (by omega : nb ≤ cost) (hcompact i d hI) hlocal

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace
