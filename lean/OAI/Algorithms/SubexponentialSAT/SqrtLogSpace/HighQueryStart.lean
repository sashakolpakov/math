import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendState
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeQueryPreparation
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLocalBounds

/-! Actual entry to each high-assignment count. The current frontend mask
survives concrete packing/arithmetic and drives the fixed zero-seed program.
The compact returned boundary is separate from the transient prefix bound. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query HashGreedyProgram.NativeRound

abbrev Data := State 40 896
abbrev Lower := State 40 768

def command : Cmd 40 896 := .call HighCountSeed.initializeProgram

def changed : List (Fin 896) := [330,788,789,790,323,791,792]

section Preparation

variable (q : LeafQueryFrontend.Query) (k : ℕ) (base : Lower) (front : Data)
  (l : Fin 8 → ℕ) (bw : Bank.Words) (packed out : Lower)
  (p : PackingCallerProgram.Problem)
  (first : MulticolorTypes.Word p.r p.Q) (rest : List (MulticolorTypes.Word p.r p.Q))
  (hfront : FrontState q k base (HighMarkedFrontend.project front) l bw)
  (hpacked : packed.stacks =
    (PackingCallerProgram.result (HighMarkedFrontend.project front) p first rest).stacks)
  {m : Circuit.Model} {hd : 0 < m.val 34}
  {M : SubexpPreparedQuartic.Modulus 3 (m.val 33)}
  {cache : RingProgram.ScalarCache 3 (m.val 33)}
  {half : RingProgram.ScalarCode 3 (m.val 33)} {e : LeafRingSetupProgram.Data}
  (hout : ArithmeticOutput packed out m hd M cache half e)

include hfront hpacked hout

/-- Concrete preparation preserves the freshly recomputed current-query mask. -/
theorem prepared_mask :
    (HighMarkedFrontend.result front out).stacks 338 =
      LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient) := by
  rw [show (338 : Fin 896) = HighMarkedFrontend.stackMap 338 from rfl,
    HighMarkedFrontend.result_stack]
  exact (NativeQueryPreparation.collector_frame
    (HighMarkedFrontend.project front) packed out p first rest hpacked hout
    338 (by decide) (by decide)).trans hfront.descending

/-- The resulting durable seed uses this query's high set, with no common
high-set assumption between different marks. -/
theorem prepared_seed_counter (rf : Fin 2 → Bool) :
    (HighCountSeed.initialized (HighMarkedFrontend.result front out) rf).stacks 789 =
      Encoding.encodeList id (List.replicate (HighMarkedFrontend.highSet q).card [false]) :=
  HighMarkedFrontend.initialized_current_counter q _ rf
    (prepared_mask q k base front l bw packed out p first rest hfront hpacked hout)

end Preparation

/-- Every immutable source and suspended selector word survives the actual
packing/arithmetic outputs. No source is assumed unread here. -/
theorem prepared_kept_frame (front : Data) (packed out : Lower)
    (p : PackingCallerProgram.Problem)
    (first : MulticolorTypes.Word p.r p.Q) (rest : List (MulticolorTypes.Word p.r p.Q))
    (hpacked : packed.stacks =
      (PackingCallerProgram.result (HighMarkedFrontend.project front) p first rest).stacks)
    {m : Circuit.Model} {hd : 0 < m.val 34}
    {M : SubexpPreparedQuartic.Modulus 3 (m.val 33)}
    {cache : RingProgram.ScalarCache 3 (m.val 33)}
    {half : RingProgram.ScalarCode 3 (m.val 33)} {e : LeafRingSetupProgram.Data}
    (hout : ArithmeticOutput packed out m hd M cache half e)
    (i : Fin 896) (hi : HashMarkedReturn.kept i = true) :
    (HighMarkedFrontend.result front out).stacks i = front.stacks i := by
  by_cases hu : 768 ≤ i.val
  · exact HighMarkedFrontend.result_upper_frame front out i hu
  · let j : Fin 768 := ⟨i.val,by omega⟩
    have hij : HighMarkedFrontend.stackMap j = i := Fin.ext rfl
    rw [←hij,HighMarkedFrontend.result_stack]
    change out.stacks j = (HighMarkedFrontend.project front).stacks j
    have hj : j = 320 ∨ j = 322 ∨ j = 700 ∨ j = 701 ∨ j = 707 ∨
        j = 708 ∨ j = 709 ∨ 744 ≤ j.val := by
      simp only [HashMarkedReturn.kept,decide_eq_true_eq,Fin.ext_iff,
        Fin.coe_ofNat_eq_mod] at hi ⊢
      dsimp [j]
      omega
    rcases hj with h | h | h | h | h | h | h | h
    · rw [h]
      exact NativeQueryPreparation.collector_frame _ packed out p first rest hpacked hout
        320 (by decide) (by decide)
    · rw [h]
      exact NativeQueryPreparation.collector_frame _ packed out p first rest hpacked hout
        322 (by decide) (by decide)
    · rw [h]
      exact NativeQueryPreparation.sources_frame _ packed out p first rest hpacked hout 700 (by decide)
    · rw [h]
      exact NativeQueryPreparation.sources_frame _ packed out p first rest hpacked hout 701 (by decide)
    · rw [h]
      exact NativeQueryPreparation.sources_frame _ packed out p first rest hpacked hout 707 (by decide)
    · rw [h]
      exact NativeQueryPreparation.sources_frame _ packed out p first rest hpacked hout 708 (by decide)
    · rw [h]
      exact NativeQueryPreparation.sources_frame _ packed out p first rest hpacked hout 709 (by decide)
    · have ha : out.stacks j = packed.stacks j := by
        apply hout.highFrame j (by omega)
        · intro he
          have hv := congrArg Fin.val he
          change j.val = 699 at hv
          omega
        · intro he
          simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,
            Fin.coe_ofNat_eq_mod] at he
          omega
      rw [ha,hpacked]
      exact PackingCallerProgram.result_frame _ p first rest j
        (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr h)

/-- The reusable lower counter and durable high counter contain the same
fresh zero tuple immediately after the actual initializer. -/
theorem initialized_lower_counter (a : Data) (rf : Fin 2 → Bool) :
    (HighCountSeed.initialized a rf).stacks 330 = (HighCountSeed.initialized a rf).stacks 789 := by
  rw [HighCountSeed.initialized_counter]
  change (HighCountInit.result (HighCountSeed.result a rf)).stacks 330 = _
  rw [HighCountInit.frame _ 330 (by decide),HighCountSeed.result_counter]

theorem initialized_kept_frame (a : Data) (rf : Fin 2 → Bool) (i : Fin 896)
    (hi : HashMarkedReturn.kept i = true) :
    (HighCountSeed.initialized a rf).stacks i = a.stacks i := by
  apply HighCountSeed.initialized_frame
  intro hc
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [HashMarkedReturn.kept,Fin.ext_iff,Fin.coe_ofNat_eq_mod] at hi

/-- Seed generation touches only scratch registers0/1 and restores the
odometer guard21. In particular the real frontend guard8 remains available. -/
theorem initialized_register_frame (a : Data) (rf : Fin 2 → Bool)
    (i : Fin 40) (hi : 2 ≤ i.val) (h21 : i ≠ 21) :
    (HighCountSeed.initialized a rf).regs i = a.regs i := by
  have h0 : i ≠ 0 := by intro h; subst i; norm_num at hi
  have h1 : i ≠ 1 := by intro h; subst i; norm_num at hi
  have hs : (HighCountSeed.result a rf).regs i = (HighCountSeed.copied a).regs i := by
    apply embedState_register_frame
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega
  calc
    _ = (HighCountSeed.result a rf).regs i := by
      simp [HighCountSeed.initialized,HighCountInit.result,HighCountInit.copied,
        HighCountInit.resetState,readRegs,h0,h1,h21]
    _ = (HighCountSeed.copied a).regs i := hs
    _ = a.regs i := by
      simp [HighCountSeed.copied,HighCountSeed.resetState,readRegs,h0,h1]

/-- The current physical high mask itself survives initialization. -/
theorem initialized_mask (a : Data) (rf : Fin 2 → Bool) :
    (HighCountSeed.initialized a rf).stacks 338 = a.stacks 338 :=
  HighCountSeed.initialized_frame a rf 338 (by decide)

/-- Only the retained zero tuple needs a new boundary-length estimate; the
initializer empties every other changed word and frames all remaining words. -/
theorem initialized_boundary (q : LeafQueryFrontend.Query) (a : Data)
    (rf : Fin 2 → Bool) (B : ℕ)
    (hm : a.stacks 338 =
      LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient))
    (hn : 4 * BinaryArithmetic.toNat q.ambient + 1 ≤ B)
    (hframe : ∀ i, i ∉ changed → (a.stacks i).length ≤ B) :
    ∀ i, ((HighCountSeed.initialized a rf).stacks i).length ≤ B := by
  have hc := (HighMarkedFrontend.initialized_current_counter_length q a rf hm).trans hn
  intro i
  by_cases hi : i = 330
  · subst i
    rw [initialized_lower_counter]
    exact hc
  · by_cases hj : i = 789
    · subst i
      exact hc
    · by_cases hz : i ∈ ([788,790,323,791,792] : List (Fin 896))
      · rw [HighCountSeed.initialized_blank a rf i hz]
        exact Nat.zero_le _
      · have hf : i ∉ changed := by
          simp only [changed,List.mem_cons,List.not_mem_nil,or_false] at *
          tauto
        rw [HighCountSeed.initialized_frame a rf i hf]
        exact hframe i hf

/-- Source-only time, full-prefix space and a separately restored compact
boundary all describe the same actual fixed seed call. The empty high set
still produces the singleton encoded zero tuple. -/
theorem resources (q : LeafQueryFrontend.Query) (a : Data) (L B D : ℕ)
    (hm : a.stacks 338 =
      LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient))
    (hL : ∀ i ∈ HighQueryLocalBounds.seedSources, (a.stacks i).length ≤ L)
    (hlocal : 12 * L + 5 ≤ D) (hD : ∀ i, (a.stacks i).length ≤ D)
    (hn : 4 * BinaryArithmetic.toNat q.ambient + 1 ≤ B)
    (hframe : ∀ i, i ∉ changed → (a.stacks i).length ≤ B) :
    ∃ steps rf, steps ≤ 110 * L + 80 ∧
      Eval command steps a (HighCountSeed.initialized a rf) ∧
      Trace (compiled command 778 777) (steps + 1)
        (a.withPC (some (compiled command 778 777).entry))
        ((HighCountSeed.initialized a rf).withPC none) ∧
      (∀ t z, t ≤ steps + 1 → Trace (compiled command 778 777) t
        (a.withPC (some (compiled command 778 777).entry)) z →
        ∀ i, (z.stacks i).length ≤ D) ∧
      (∀ i, ((HighCountSeed.initialized a rf).stacks i).length ≤ B) ∧
      (HighCountSeed.initialized a rf).stacks 789 =
        Encoding.encodeList id (List.replicate (HighMarkedFrontend.highSet q).card [false]) ∧
      (∀ i ∈ ([788,790,323,791,792] : List (Fin 896)),
        (HighCountSeed.initialized a rf).stacks i = []) ∧
      (HighCountSeed.initialized a rf).regs 21 = true ∧
      (∀ i, HashMarkedReturn.kept i = true →
        (HighCountSeed.initialized a rf).stacks i = a.stacks i) := by
  obtain ⟨steps,rf,ht,he,hprefix⟩ := HighQueryLocalBounds.seed_resources a L D hL hlocal hD
  refine ⟨steps,rf,ht,he,compiled_halt_trace he 778 777,?_,
    initialized_boundary q a rf B hm hn hframe,
    HighMarkedFrontend.initialized_current_counter q a rf hm,
    HighCountSeed.initialized_blank a rf,HighCountSeed.initialized_guard a rf,
    initialized_kept_frame a rf⟩
  exact StructuredSpace.compiled_halt_stack_bound he 778 777 hprefix.bound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart
