import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTaylorCacheCalls
import OAI.Algorithms.SubexponentialSAT.SubexpNodeLiftData

namespace OAI.Algorithms

/-! Typed execution of the nested Taylor-cache map. Every row callback is
the concrete shift/framing program; the typed schemas occur only in proofs. -/

namespace SubexponentialSAT.SubexpTaylorCacheMap

open BitProgram StructuredCalls SubexpScanPrimitives SubexpHornerControl
open SubexpTaylorControl SubexpTaylorCacheControl SubexpTaylorCacheCalls
open SubexpLiftRing SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem mapped_budget_le {C : Type*} (encode : C → List Bool) (items : List C)
    (cost width : ℕ) (h : ∀ x ∈ items, (encode x).length ≤ width) :
    RecordPrograms.budget (fun _ => cost) (items.map encode) ≤
      items.length * (6 * width + cost + 7) := by
  induction items with
  | nil => simp [RecordPrograms.budget]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons, RecordPrograms.budget, List.length_cons]
      nlinarith

theorem mapped_stream_length_le {C : Type*} (encode : C → List Bool) (items : List C)
    (width : ℕ) (h : ∀ x ∈ items, (encode x).length ≤ width) :
    (recordStream (items.map encode)).length ≤ items.length * (2 * width + 2) := by
  induction items with
  | nil => simp [recordStream]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      change (SubexpTaylorFrames.recordBytes (encode x) ++
        recordStream (xs.map encode)).length ≤ _
      simp only [List.length_append, SubexpTaylorFrames.recordBytes, List.length_cons,
        Encoding.length_frame]
      nlinarith

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

abbrev Code := SubexpTaylorRow.Code p μ
abbrev rowBytes (P : List (Code p μ)) := encodeList SubexpTaylorRow.flat P
abbrev cacheBytes (t theta : Code p μ) (N : ℕ) (P : List (Code p μ)) :=
  Encoding.encodeList SubexpTaylorRow.flat (SubexpTaylorRow.cache p μ M t theta N P)

omit [Fact p.Prime] in
theorem rowBytes_injective (hμ : 0 < μ) : Function.Injective (rowBytes p μ) := by
  have hB : 0 < baseWidth p μ := Nat.mul_pos hμ (Nat.succ_pos _)
  have hf : Function.Injective (SubexpTaylorRow.flat (B := baseWidth p μ)) := by
    intro a b hab
    apply SubexpNodeLiftData.encode_injective hB
    simpa [SubexpTaylorRow.flat, SubexpQuarticFlatMul.flat,
      SubexpQuarticFlatMul.wordLists, FourWordPrograms.flatWords, Quad.toFn,
      SubexpNodeLiftData.encode, List.append_assoc] using hab
  let code : StackEncoding.BlockCode (Code p μ) :=
    ⟨4 * baseWidth p μ, Nat.mul_pos (by decide) hB,
      SubexpTaylorRow.flat, SubexpQuarticFlatMul.flat_length, hf⟩
  intro P Q h
  apply StackEncoding.encodeDataStack_injective code
  simpa only [StackEncoding.encodeDataStack_eq_flatMap, code, rowBytes, encodeList] using h

def invariant (base : Words) (N : ℕ) (d : Data) : Prop :=
  clean base d ∧ d.stacks 101 = List.replicate N true ∧ d.stacks 109 = [] ∧ d.stacks 110 = []

def coordinateEffect (t theta : Code p μ) (N : ℕ)
    (bits : List Bool) (a b : Data) : Prop :=
  (∀ P, rowBytes p μ P = bits → b.stacks 106 =
    (SubexpTaylorFrames.recordBytes (cacheBytes p μ M t theta N P)).reverse ++ a.stacks 106) ∧
  (∀ i : Fin 112, i ≠ 105 → i ≠ 87 → i ≠ 106 → b.stacks i = a.stacks i) ∧
  (∀ i : Fin 14, 11 ≤ i.val → b.regs i = a.regs i)

def validRow (R : ℕ) (bits : List Bool) : Prop :=
  ∃ P : List (Code p μ), P.length ≤ R ∧ rowBytes p μ P = bits

theorem clean_coordinateState (base : Words) (d : Data) (hc : clean base d)
    (v pr f : Bool) (tail : List Bool) :
    clean base (RecordPrograms.state coordinatePorts d v pr f tail []) := by
  intro i
  have hn105 := rowStacks_ne_high i (105 : Fin 112) (by decide)
  by_cases h87 : i = 87
  · subst i; simp [RecordPrograms.state, coordinatePorts, rowStacks]
  · have hn87 : rowStacks i ≠ 87 := by
      change rowStacks i ≠ rowStacks 87
      exact fun h => h87 (rowStacks.injective h)
    simpa only [RecordPrograms.state, coordinatePorts,
      Function.update_of_ne hn105, Function.update_of_ne hn87] using hc i

theorem invariant_coordinateState (base : Words) (N : ℕ) (d : Data)
    (hi : invariant base N d) (v pr f : Bool) (tail : List Bool) :
    invariant base N (RecordPrograms.state coordinatePorts d v pr f tail []) := by
  refine ⟨clean_coordinateState base d hi.1 v pr f tail, ?_, ?_, ?_⟩
  · simpa [RecordPrograms.state, coordinatePorts] using hi.2.1
  · simpa [RecordPrograms.state, coordinatePorts] using hi.2.2.1
  · simpa [RecordPrograms.state, coordinatePorts] using hi.2.2.2

theorem coordinate_contract (hμ : 0 < μ) (t theta : Code p μ)
    (width blockWidth : List Bool) (hw : width.length = baseWidth p μ)
    (hblock : blockWidth.length = 4 * baseWidth p μ) (N R : ℕ) :
    RecordPrograms.CallbackContractWithOn coordinatePorts coordinateCallback (fun _ => false)
      (fun _ => rowCallbackBudget R N (baseWidth p μ))
      (invariant (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) N)
      (coordinateEffect p μ M t theta N) (validRow p μ R) := by
  intro bits tail before hv hi
  obtain ⟨P, hP, rfl⟩ := hv
  let d := RecordPrograms.state coordinatePorts before false true false tail []
  have hd := invariant_coordinateState _ N before hi false true false tail
  have hinput : RecordPrograms.state coordinatePorts before false true false tail
      (rowBytes p μ P).reverse = withRow d (rowBytes p μ P).reverse [] [] := by
    apply state_ext
    · rfl
    · funext i
      have h88 := clean_88 _ before hi.1
      have h89 := clean_89 _ before hi.1
      by_cases hi87 : i = 87 <;> by_cases hi88 : i = 88 <;> by_cases hi89 : i = 89 <;>
        simp [d, RecordPrograms.state, coordinatePorts, withRow,
          Function.update_apply, hi87, hi88, hi89, h88, h89]
  obtain ⟨n, hn, regs, hregs, hr⟩ := coordinate_eval p μ M hμ t theta
    width blockWidth hw hblock N P d hd.1 hd.2.1 hd.2.2.1 hd.2.2.2
  let next : Data := ⟨regs, Function.update d.stacks 106
    ((SubexpTaylorFrames.recordBytes (cacheBytes p μ M t theta N P)).reverse ++ d.stacks 106)⟩
  have hnext : invariant (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) N next := by
    refine ⟨clean_reg_change _ _ regs (clean_update_high _ d hd.1 106 (by decide) _), ?_, ?_, ?_⟩
    · simpa [next] using hd.2.1
    · simpa [next] using hd.2.2.1
    · simpa [next] using hd.2.2.2
  have hfinish : RecordPrograms.state coordinatePorts next false true false tail [] = next := by
    apply RecordPrograms.state_eq_self
    · exact (hregs 8 (by decide)).trans (RecordPrograms.state_tag coordinatePorts before _ _ _ _ _)
    · exact (hregs 9 (by decide)).trans (RecordPrograms.state_present coordinatePorts before _ _ _ _ _)
    · exact (hregs 10 (by decide)).trans (RecordPrograms.state_found coordinatePorts before _ _ _ _ _)
    · simp [next, d, RecordPrograms.state, coordinatePorts]
    · exact clean_87 _ next hnext.1
  refine ⟨n, next, hn.trans (rowCallbackBudget_mono hP N _), hnext, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro Q hQ
      have hQP := rowBytes_injective p μ hμ hQ
      subst Q
      simp [next, d, RecordPrograms.state, coordinatePorts]
    · intro i h105 h87 h106
      simp [next, d, RecordPrograms.state, coordinatePorts, h105, h87, h106]
    · intro i h11
      change regs i = before.regs i
      rw [hregs i (by omega)]
      have h8 : i ≠ 8 := by intro h; subst i; norm_num at h11
      have h9 : i ≠ 9 := by intro h; subst i; norm_num at h11
      have h10 : i ≠ 10 := by intro h; subst i; norm_num at h11
      simp [d, RecordPrograms.state, coordinatePorts, h8, h9, h10]
  · rw [hfinish, hinput]
    exact hr

def coordinateBudget (rows R N B : ℕ) : ℕ :=
  3 + rows * (24 * B * R + rowCallbackBudget R N B + 7) +
    (3 * (rows * (2 * ((8 * B + 2) * N + 1) + 2)) + 8)

theorem coordinate_iterations (hμ : 0 < μ) (t theta : Code p μ)
    (width blockWidth : List Bool) (hw : width.length = baseWidth p μ)
    (hblock : blockWidth.length = 4 * baseWidth p μ) (N R : ℕ)
    (rows : List (List (Code p μ))) (hR : ∀ P ∈ rows, P.length ≤ R)
    (d : Data) (hi : invariant (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) N d)
    (hs : d.stacks 105 = Encoding.encodeList (rowBytes p μ) rows) (ha : d.stacks 106 = []) :
    ∃ n ≤ 3 + rows.length * (24 * baseWidth p μ * R + rowCallbackBudget R N (baseWidth p μ) + 7),
      ∃ next : Data,
      invariant (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) N next ∧
      next.stacks = Function.update (Function.update d.stacks 105 []) 106
        (recordStream (rows.map (cacheBytes p μ M t theta N))).reverse ∧
      (∀ i : Fin 14, 11 ≤ i.val → next.regs i = d.regs i) ∧
      Eval (RecordPrograms.iterate coordinatePorts coordinateCallback) n d next := by
  have hv : ∀ bits ∈ rows.map (rowBytes p μ), validRow p μ R bits := by
    intro bits hb
    obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hb
    exact ⟨P, hR P hP, rfl⟩
  obtain ⟨n, next, hn, hnext, hvisit, hrun⟩ := RecordPrograms.iterate_run_with_on
    coordinatePorts coordinateCallback (fun _ => false)
    (fun _ => rowCallbackBudget R N (baseWidth p μ))
    (invariant (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) N)
    (coordinateEffect p μ M t theta N) (validRow p μ R)
    (coordinate_contract p μ M hμ t theta width blockWidth hw hblock N R)
    (rows.map (rowBytes p μ)) [] d hv hi (d.regs 8) (d.regs 9) (d.regs 10)
  have hstart : RecordPrograms.state coordinatePorts d (d.regs 8) (d.regs 9) (d.regs 10)
      (Encoding.encodeList id (rows.map (rowBytes p μ)) ++ []) [] = d := by
    apply RecordPrograms.state_eq_self <;> try rfl
    · change d.stacks 105 = Encoding.encodeList id (rows.map (rowBytes p μ)) ++ []
      simpa only [List.append_nil, SubexpTaylorRow.encode_map] using hs
    · exact clean_87 _ d hi.1
  rw [hstart] at hrun
  have hfalse : (rows.map (rowBytes p μ)).any (fun _ => false) = false := by simp
  rw [hfalse, unread_false] at hrun
  let final := RecordPrograms.state coordinatePorts next false true false [] []
  have hfinal := invariant_coordinateState _ N next hnext false true false []
  have hpacked := visits_packed (rowBytes p μ) (cacheBytes p μ M t theta N) 106
    (coordinateEffect p μ M t theta N) (fun _ _ _ h => h.1) rows d next hvisit
  have hframe : ∀ i : Fin 112, i ≠ 105 → i ≠ 87 → i ≠ 106 → next.stacks i = d.stacks i := by
    intro i h105 h87 h106
    exact visits_unchanged (fun a => a.stacks i) (coordinateEffect p μ M t theta N)
      (fun _ _ _ h => h.2.1 i h105 h87 h106) _ _ _ hvisit
  have hreg : ∀ i : Fin 14, 11 ≤ i.val → next.regs i = d.regs i := by
    intro i hi
    exact visits_unchanged (fun a => a.regs i) (coordinateEffect p μ M t theta N)
      (fun _ _ _ h => h.2.2 i hi) _ _ _ hvisit
  refine ⟨n, ?_, final, hfinal, ?_, ?_, hrun⟩
  · have hb : RecordPrograms.budget (fun _ => rowCallbackBudget R N (baseWidth p μ))
        (rows.map (rowBytes p μ)) ≤
        rows.length * (24 * baseWidth p μ * R + rowCallbackBudget R N (baseWidth p μ) + 7) := by
      have h := mapped_budget_le (rowBytes p μ) rows
        (rowCallbackBudget R N (baseWidth p μ)) (R * (4 * baseWidth p μ)) (by
          intro P hP
          rw [show (rowBytes p μ P).length = P.length * (4 * baseWidth p μ) from
            SubexpTaylorOuter.encodeList_length _ _ SubexpQuarticFlatMul.flat_length P]
          exact Nat.mul_le_mul_right _ (hR P hP))
      convert h using 1
      ring
    omega
  · funext i
    by_cases hi105 : i = 105
    · subst i; simp [final, RecordPrograms.state, coordinatePorts]
    by_cases hi87 : i = 87
    · subst i
      simp [final, RecordPrograms.state, coordinatePorts, clean_87 _ d hi.1]
    by_cases hi106 : i = 106
    · subst i
      simpa [final, RecordPrograms.state, coordinatePorts, ha] using hpacked
    · simpa [final, RecordPrograms.state, coordinatePorts, hi105, hi87, hi106]
        using hframe i hi105 hi87 hi106
  · intro i h11
    have h8 : i ≠ 8 := by intro h; subst i; norm_num at h11
    have h9 : i ≠ 9 := by intro h; subst i; norm_num at h11
    have h10 : i ≠ 10 := by intro h; subst i; norm_num at h11
    simpa [final, RecordPrograms.state, coordinatePorts, h8, h9, h10] using hreg i h11

omit [Fact p.Prime] in
theorem cache_stream_length (t theta : Code p μ) (N : ℕ)
    (rows : List (List (Code p μ))) :
    (recordStream (rows.map (cacheBytes p μ M t theta N))).length =
      rows.length * (2 * ((8 * baseWidth p μ + 2) * N + 1) + 2) := by
  induction rows with
  | nil => simp [recordStream]
  | cons P rows ih =>
      change ((SubexpTaylorFrames.recordBytes (cacheBytes p μ M t theta N P)) ++
        recordStream (rows.map (cacheBytes p μ M t theta N))).length = _
      simp only [List.length_append, SubexpTaylorFrames.recordBytes, List.length_cons,
        Encoding.length_frame, cacheBytes, SubexpTaylorRow.cache_encode_length,
        ih, List.length_cons]
      ring

theorem coordinates_eval (hμ : 0 < μ) (t theta : Code p μ)
    (width blockWidth : List Bool) (hw : width.length = baseWidth p μ)
    (hblock : blockWidth.length = 4 * baseWidth p μ) (N R : ℕ)
    (rows : List (List (Code p μ))) (hR : ∀ P ∈ rows, P.length ≤ R)
    (d : Data) (hi : invariant (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) N d)
    (hs : d.stacks 105 = Encoding.encodeList (rowBytes p μ) rows)
    (ha : d.stacks 106 = []) (ho : d.stacks 107 = []) :
    ∃ n ≤ coordinateBudget rows.length R N (baseWidth p μ), ∃ next : Data,
      invariant (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) N next ∧
      next.stacks = Function.update (Function.update d.stacks 105 []) 107
        (Encoding.encodeList (cacheBytes p μ M t theta N) rows) ∧
      (∀ i : Fin 14, 11 ≤ i.val → next.regs i = d.regs i) ∧
      Eval coordinates n d next := by
  obtain ⟨n, hn, middle, hm, hms, hmr, hr⟩ := coordinate_iterations p μ M hμ t theta
    width blockWidth hw hblock N R rows hR d hi hs ha
  have hf := finishList_eval 106 107 (by decide) middle
  let final := finishResult 106 107 middle
  have hp : (middle.stacks 106).length =
      rows.length * (2 * ((8 * baseWidth p μ + 2) * N + 1) + 2) := by
    rw [hms]
    simp only [Function.update_self, List.length_reverse, cache_stream_length]
  have hout : final.stacks = Function.update (Function.update d.stacks 105 []) 107
      (Encoding.encodeList (cacheBytes p μ M t theta N) rows) := by
    have hencode : Encoding.encodeList (cacheBytes p μ M t theta N) rows =
        recordStream (rows.map (cacheBytes p μ M t theta N)) ++ [false] := by
      rw [← SubexpTaylorRow.encode_map, encodeList_recordStream]
    funext i
    by_cases h105 : i = 105 <;> by_cases h106 : i = 106 <;> by_cases h107 : i = 107 <;>
      simp [final, finishResult, hms,
        h105, h106, h107, ha, ho, hencode]
  have hi' : invariant (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) N final := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      rw [hout]
      have h105 := rowStacks_ne_high i (105 : Fin 112) (by decide)
      have h107 := rowStacks_ne_high i (107 : Fin 112) (by decide)
      simpa only [Function.update_of_ne h105, Function.update_of_ne h107] using hi.1 i
    · simpa only [hout, Function.update_of_ne (show (101 : Fin 112) ≠ 107 by decide),
        Function.update_of_ne (show (101 : Fin 112) ≠ 105 by decide)] using hi.2.1
    · simpa only [hout, Function.update_of_ne (show (109 : Fin 112) ≠ 107 by decide),
        Function.update_of_ne (show (109 : Fin 112) ≠ 105 by decide)] using hi.2.2.1
    · simpa only [hout, Function.update_of_ne (show (110 : Fin 112) ≠ 107 by decide),
        Function.update_of_ne (show (110 : Fin 112) ≠ 105 by decide)] using hi.2.2.2
  refine ⟨n + (3 * (middle.stacks 106).length + 8), ?_, final, hi', hout, ?_, hr.seq hf⟩
  · rw [hp]
    unfold coordinateBudget
    omega
  · intro i h11
    have h0 : i ≠ 0 := by intro h; subst i; norm_num at h11
    have h1 : i ≠ 1 := by intro h; subst i; norm_num at h11
    exact (StackRoutines.readRegs_frame middle.regs 0 1 i none h0 h1).trans (hmr i h11)

abbrev incidenceBytes (rows : List (List (Code p μ))) :=
  Encoding.encodeList (rowBytes p μ) rows

abbrev incidenceCacheBytes (t theta : Code p μ) (N : ℕ)
    (rows : List (List (Code p μ))) :=
  Encoding.encodeList (cacheBytes p μ M t theta N) rows

def incidenceInputBound (C R B : ℕ) : ℕ := (8 * B * R + 2) * C + 1
def incidenceOutputBound (C N B : ℕ) : ℕ := (2 * ((8 * B + 2) * N + 1) + 2) * C + 1
def incidenceCallbackBudget (C R N B : ℕ) : ℕ :=
  3 * incidenceInputBound C R B + coordinateBudget C R N B +
    14 * incidenceOutputBound C N B + 22

omit [Fact p.Prime] in
theorem incidenceBytes_length_le (R : ℕ) (rows : List (List (Code p μ)))
    (hR : ∀ P ∈ rows, P.length ≤ R) :
    (incidenceBytes p μ rows).length ≤ incidenceInputBound rows.length R (baseWidth p μ) := by
  have h := Encoding.length_encodeList_upper (rowBytes p μ) rows (R * (4 * baseWidth p μ)) (by
    intro P hP
    rw [show (rowBytes p μ P).length = P.length * (4 * baseWidth p μ) from
      SubexpTaylorOuter.encodeList_length _ _ SubexpQuarticFlatMul.flat_length P]
    exact Nat.mul_le_mul_right _ (hR P hP))
  convert h using 1
  unfold incidenceInputBound
  ring

omit [Fact p.Prime] in
theorem incidenceCacheBytes_length (t theta : Code p μ) (N : ℕ)
    (rows : List (List (Code p μ))) :
    (incidenceCacheBytes p μ M t theta N rows).length =
      incidenceOutputBound rows.length N (baseWidth p μ) := by
  change (Encoding.encodeList (cacheBytes p μ M t theta N) rows).length = _
  rw [← SubexpTaylorRow.encode_map, encodeList_recordStream, List.length_append,
    cache_stream_length]
  simp [incidenceOutputBound]
  ring

theorem incidenceCallbackBudget_mono {C D : ℕ} (h : C ≤ D) (R N B : ℕ) :
    incidenceCallbackBudget C R N B ≤ incidenceCallbackBudget D R N B := by
  unfold incidenceCallbackBudget incidenceInputBound incidenceOutputBound coordinateBudget
  gcongr

def incidenceInvariant (base : Words) (N : ℕ) (d : Data) : Prop :=
  invariant base N d ∧ d.stacks 105 = [] ∧ d.stacks 106 = [] ∧ d.stacks 107 = []

theorem invariant_transfer_inner (base : Words) (N : ℕ) (d : Data)
    (h : invariant base N d) :
    invariant base N (afterTransfer d 104 105 0 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    have h104 := rowStacks_ne_high i (104 : Fin 112) (by decide)
    have h105 := rowStacks_ne_high i (105 : Fin 112) (by decide)
    simpa [afterTransfer, StackRoutines.transferStacks, h104, h105] using h.1 i
  · simpa [afterTransfer, StackRoutines.transferStacks] using h.2.1
  · simpa [afterTransfer, StackRoutines.transferStacks] using h.2.2.1
  · simpa [afterTransfer, StackRoutines.transferStacks] using h.2.2.2

/-- One actual outer callback: restore the parsed inner list, run every
coordinate row, frame the resulting inner cache, and accumulate its bytes. -/
theorem incidence_eval (hμ : 0 < μ) (t theta : Code p μ)
    (width blockWidth : List Bool) (hw : width.length = baseWidth p μ)
    (hblock : blockWidth.length = 4 * baseWidth p μ) (N R : ℕ)
    (rows : List (List (Code p μ))) (hR : ∀ P ∈ rows, P.length ≤ R)
    (d : Data)
    (hi : incidenceInvariant (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) N d)
    (hinput : d.stacks 104 = (incidenceBytes p μ rows).reverse) :
    ∃ n ≤ incidenceCallbackBudget rows.length R N (baseWidth p μ),
      ∃ regs : Fin 14 → Bool, (∀ i : Fin 14, 11 ≤ i.val → regs i = d.regs i) ∧
      Eval incidenceCallback n d
        ⟨regs, Function.update (Function.update d.stacks 104 []) 108
          ((SubexpTaylorFrames.recordBytes (incidenceCacheBytes p μ M t theta N rows)).reverse ++
            d.stacks 108)⟩ := by
  let a := afterTransfer d 104 105 0 1
  have h1 := transfer_eval d 104 105 0 1 (by decide) (by decide)
  have ha := invariant_transfer_inner _ N d hi.1
  have ha105 : a.stacks 105 = incidenceBytes p μ rows := by
    simp [a, afterTransfer, StackRoutines.transferStacks, hinput, hi.2.1]
  have ha106 : a.stacks 106 = [] := by
    simpa [a, afterTransfer, StackRoutines.transferStacks] using hi.2.2.1
  have ha107 : a.stacks 107 = [] := by
    simpa [a, afterTransfer, StackRoutines.transferStacks] using hi.2.2.2
  obtain ⟨nc, hnc, b, hb, hbs, hbr, h2⟩ := coordinates_eval p μ M hμ t theta
    width blockWidth hw hblock N R rows hR a ha ha105 ha106 ha107
  let out := incidenceCacheBytes p μ M t theta N rows
  let c := afterTransfer b 107 109 0 1
  let e := writerResult c
  let f := afterTransfer e 110 108 0 1
  have h3 := transfer_eval b 107 109 0 1 (by decide) (by decide)
  have h4 := writeRecord_eval c
  have h5 := transfer_eval e 110 108 0 1 (by decide) (by decide)
  have hb107 : b.stacks 107 = out := by simp [hbs, out]
  have hc109 : c.stacks 109 = out.reverse := by
    simp [c, afterTransfer, StackRoutines.transferStacks, hb107, hb.2.2.1]
  have hc110 : c.stacks 110 = [] := by
    simpa [c, afterTransfer, StackRoutines.transferStacks] using hb.2.2.2
  have he110 : e.stacks 110 = SubexpTaylorFrames.recordBytes out := by
    simp only [e, writerResult, Function.update_self, hc109,
      List.reverse_reverse, hc110, List.append_nil]
  have hfs : f.stacks = Function.update (Function.update d.stacks 104 []) 108
      ((SubexpTaylorFrames.recordBytes out).reverse ++ d.stacks 108) := by
    funext i
    by_cases h104 : i = 104 <;> by_cases h105 : i = 105 <;> by_cases h107 : i = 107 <;>
      by_cases h108 : i = 108 <;> by_cases h109 : i = 109 <;> by_cases h110 : i = 110 <;>
      simp [f, e, c, writerResult, afterTransfer, StackRoutines.transferStacks,
        hbs, a, out, h104, h105, h107, h108, h109, h110,
        hi.1.2.2.1, hi.1.2.2.2, hi.2.1, hi.2.2.2]
  refine ⟨(3 * (d.stacks 104).length + 3) +
    (nc + ((3 * (b.stacks 107).length + 3) +
      ((5 * (c.stacks 109).length + 7) + (3 * (e.stacks 110).length + 3)))),
    ?_, f.regs, ?_, ?_⟩
  · have hin := incidenceBytes_length_le p μ R rows hR
    have hout := incidenceCacheBytes_length p μ M t theta N rows
    rw [hinput, List.length_reverse, hb107, hc109, List.length_reverse, he110]
    simp only [SubexpTaylorFrames.recordBytes, List.length_cons, Encoding.length_frame]
    change _ ≤ incidenceCallbackBudget rows.length R N (baseWidth p μ)
    change out.length = _ at hout
    rw [hout]
    unfold incidenceCallbackBudget
    omega
  · intro i h11
    have h0 : i ≠ 0 := by intro h; subst i; norm_num at h11
    have h1' : i ≠ 1 := by intro h; subst i; norm_num at h11
    have hf : f.regs i = b.regs i := by
      simp [f, e, c, afterTransfer, writerResult, readRegs, h0, h1']
    exact hf.trans ((hbr i h11).trans
      (StackRoutines.readRegs_frame d.regs 0 1 i none h0 h1'))
  · have hf : f = ⟨f.regs, Function.update (Function.update d.stacks 104 []) 108
        ((SubexpTaylorFrames.recordBytes out).reverse ++ d.stacks 108)⟩ := state_ext rfl hfs
    have he := h1.seq (h2.seq (h3.seq (h4.seq h5)))
    change Eval incidenceCallback _ d f at he
    rw [hf] at he
    exact he

theorem incidenceInvariant_state (base : Words) (N : ℕ) (d : Data)
    (hi : incidenceInvariant base N d) (v pr f : Bool) (tail payload : List Bool) :
    incidenceInvariant base N (RecordPrograms.state incidencePorts d v pr f tail payload) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i
    have h103 := rowStacks_ne_high i (103 : Fin 112) (by decide)
    have h104 := rowStacks_ne_high i (104 : Fin 112) (by decide)
    simpa [RecordPrograms.state, incidencePorts, h103, h104] using hi.1.1 i
  · simpa [RecordPrograms.state, incidencePorts] using hi.1.2.1
  · simpa [RecordPrograms.state, incidencePorts] using hi.1.2.2.1
  · simpa [RecordPrograms.state, incidencePorts] using hi.1.2.2.2
  · simpa [RecordPrograms.state, incidencePorts] using hi.2.1
  · simpa [RecordPrograms.state, incidencePorts] using hi.2.2.1
  · simpa [RecordPrograms.state, incidencePorts] using hi.2.2.2

def incidenceEffect (t theta : Code p μ) (N : ℕ) (bits : List Bool) (a b : Data) : Prop :=
  (∀ rows, incidenceBytes p μ rows = bits → b.stacks 108 =
    (SubexpTaylorFrames.recordBytes (incidenceCacheBytes p μ M t theta N rows)).reverse ++
      a.stacks 108) ∧
  (∀ i : Fin 112, i ≠ 103 → i ≠ 104 → i ≠ 108 → b.stacks i = a.stacks i)

def validIncidence (C R : ℕ) (bits : List Bool) : Prop :=
  ∃ rows : List (List (Code p μ)), rows.length ≤ C ∧
    (∀ P ∈ rows, P.length ≤ R) ∧ incidenceBytes p μ rows = bits

theorem incidence_contract (hμ : 0 < μ) (t theta : Code p μ)
    (width blockWidth : List Bool) (hw : width.length = baseWidth p μ)
    (hblock : blockWidth.length = 4 * baseWidth p μ) (N C R : ℕ) :
    RecordPrograms.CallbackContractWithOn incidencePorts incidenceCallback (fun _ => false)
      (fun _ => incidenceCallbackBudget C R N (baseWidth p μ))
      (incidenceInvariant (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) N)
      (incidenceEffect p μ M t theta N) (validIncidence p μ C R) := by
  intro bits tail before hv hi
  obtain ⟨rows, hC, hR, rfl⟩ := hv
  let d := RecordPrograms.state incidencePorts before false true false tail
    (incidenceBytes p μ rows).reverse
  have hd := incidenceInvariant_state _ N before hi false true false tail
    (incidenceBytes p μ rows).reverse
  obtain ⟨n, hn, regs, hregs, hr⟩ := incidence_eval p μ M hμ t theta
    width blockWidth hw hblock N R rows hR d hd
    (RecordPrograms.state_payload _ _ _ _ _ _ _)
  let next : Data := ⟨regs, Function.update (Function.update d.stacks 104 []) 108
    ((SubexpTaylorFrames.recordBytes (incidenceCacheBytes p μ M t theta N rows)).reverse ++
      d.stacks 108)⟩
  have hnext : incidenceInvariant (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) N next := by
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro i
      have h104 := rowStacks_ne_high i (104 : Fin 112) (by decide)
      have h108 := rowStacks_ne_high i (108 : Fin 112) (by decide)
      simpa [next, h104, h108] using hd.1.1 i
    · simpa [next] using hd.1.2.1
    · simpa [next] using hd.1.2.2.1
    · simpa [next] using hd.1.2.2.2
    · simpa [next] using hd.2.1
    · simpa [next] using hd.2.2.1
    · simpa [next] using hd.2.2.2
  have hfinish : RecordPrograms.state incidencePorts next false true false tail [] = next := by
    apply RecordPrograms.state_eq_self
    · exact (hregs 11 (by decide)).trans (RecordPrograms.state_tag incidencePorts before _ _ _ _ _)
    · exact (hregs 12 (by decide)).trans (RecordPrograms.state_present incidencePorts before _ _ _ _ _)
    · exact (hregs 13 (by decide)).trans (RecordPrograms.state_found incidencePorts before _ _ _ _ _)
    · simp [next, d, RecordPrograms.state, incidencePorts]
    · simp [next, incidencePorts]
  refine ⟨n, next, hn.trans (incidenceCallbackBudget_mono hC R N _), hnext, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro other hother
      have heq := Encoding.encodeList_injective (rowBytes_injective p μ hμ) hother
      subst other
      simp [next, d, RecordPrograms.state, incidencePorts]
    · intro i h103 h104 h108
      simp [next, d, RecordPrograms.state, incidencePorts, h103, h104, h108]
  · rw [hfinish]
    exact hr

def incidenceIterationBudget (m C R N B : ℕ) : ℕ :=
  3 + m * (6 * incidenceInputBound C R B + incidenceCallbackBudget C R N B + 7)

theorem incidence_iterations (hμ : 0 < μ) (t theta : Code p μ)
    (width blockWidth : List Bool) (hw : width.length = baseWidth p μ)
    (hblock : blockWidth.length = 4 * baseWidth p μ) (N C R : ℕ)
    (rows : List (List (List (Code p μ))))
    (hC : ∀ coordinates ∈ rows, coordinates.length ≤ C)
    (hR : ∀ coordinates ∈ rows, ∀ P ∈ coordinates, P.length ≤ R)
    (d : Data)
    (hi : incidenceInvariant (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) N d)
    (hs : d.stacks 103 = Encoding.encodeList (incidenceBytes p μ) rows)
    (hp : d.stacks 104 = []) (ha : d.stacks 108 = []) :
    ∃ n ≤ incidenceIterationBudget rows.length C R N (baseWidth p μ), ∃ next : Data,
      incidenceInvariant (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) N next ∧
      next.stacks = Function.update (Function.update d.stacks 103 []) 108
        (recordStream (rows.map (incidenceCacheBytes p μ M t theta N))).reverse ∧
      Eval (RecordPrograms.iterate incidencePorts incidenceCallback) n d next := by
  have hv : ∀ bits ∈ rows.map (incidenceBytes p μ), validIncidence p μ C R bits := by
    intro bits h
    obtain ⟨coordinates, hc, rfl⟩ := List.mem_map.mp h
    exact ⟨coordinates, hC coordinates hc, hR coordinates hc, rfl⟩
  obtain ⟨n, next, hn, hnext, hvisit, hrun⟩ := RecordPrograms.iterate_run_with_on
    incidencePorts incidenceCallback (fun _ => false)
    (fun _ => incidenceCallbackBudget C R N (baseWidth p μ))
    (incidenceInvariant (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) N)
    (incidenceEffect p μ M t theta N) (validIncidence p μ C R)
    (incidence_contract p μ M hμ t theta width blockWidth hw hblock N C R)
    (rows.map (incidenceBytes p μ)) [] d hv hi (d.regs 11) (d.regs 12) (d.regs 13)
  have hstart : RecordPrograms.state incidencePorts d (d.regs 11) (d.regs 12) (d.regs 13)
      (Encoding.encodeList id (rows.map (incidenceBytes p μ)) ++ []) [] = d := by
    apply RecordPrograms.state_eq_self <;> try rfl
    · change d.stacks 103 = Encoding.encodeList id (rows.map (incidenceBytes p μ)) ++ []
      simpa only [List.append_nil, SubexpTaylorRow.encode_map] using hs
    · exact hp
  rw [hstart] at hrun
  have hfalse : (rows.map (incidenceBytes p μ)).any (fun _ => false) = false := by simp
  rw [hfalse, unread_false] at hrun
  let final := RecordPrograms.state incidencePorts next false true false [] []
  have hfinal := incidenceInvariant_state _ N next hnext false true false [] []
  have hpacked := visits_packed (incidenceBytes p μ) (incidenceCacheBytes p μ M t theta N) 108
    (incidenceEffect p μ M t theta N) (fun _ _ _ h => h.1) rows d next hvisit
  have hframe : ∀ i : Fin 112, i ≠ 103 → i ≠ 104 → i ≠ 108 → next.stacks i = d.stacks i := by
    intro i h103 h104 h108
    exact visits_unchanged (fun a => a.stacks i) (incidenceEffect p μ M t theta N)
      (fun _ _ _ h => h.2 i h103 h104 h108) _ _ _ hvisit
  have hlength : ∀ coordinates ∈ rows, (incidenceBytes p μ coordinates).length ≤
      incidenceInputBound C R (baseWidth p μ) := by
    intro coordinates hc
    apply (incidenceBytes_length_le p μ R coordinates (hR coordinates hc)).trans
    unfold incidenceInputBound
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (hC coordinates hc)) 1
  have hbudget := mapped_budget_le (incidenceBytes p μ) rows
    (incidenceCallbackBudget C R N (baseWidth p μ)) (incidenceInputBound C R (baseWidth p μ)) hlength
  refine ⟨n, hn.trans (Nat.add_le_add_left hbudget 3), final, hfinal, ?_, hrun⟩
  funext i
  by_cases h103 : i = 103
  · subst i; simp [final, RecordPrograms.state, incidencePorts]
  by_cases h104 : i = 104
  · subst i; simp [final, RecordPrograms.state, incidencePorts, hp]
  by_cases h108 : i = 108
  · subst i
    simpa [final, RecordPrograms.state, incidencePorts, ha] using hpacked
  · simpa [final, RecordPrograms.state, incidencePorts, h103, h104, h108]
      using hframe i h103 h104 h108

def tableBudget (m C R N B : ℕ) : ℕ :=
  7 * (1 + (2 * incidenceInputBound C R B + 2) * m) + 5 +
    incidenceIterationBudget m C R N B +
      (3 * (m * (2 * incidenceOutputBound C N B + 2)) + 8) + 1

def caches (t theta : Code p μ) (N : ℕ)
    (rows : List (List (List (Code p μ)))) : List (List (List (Code p μ))) :=
  rows.map (List.map (SubexpTaylorRow.cache p μ M t theta N))

theorem encodeList_map_eq {A B : Type*} (encode : B → List Bool) (f : A → B) (xs : List A) :
    Encoding.encodeList encode (xs.map f) = Encoding.encodeList (fun x => encode (f x)) xs := by
  induction xs <;> simp [Encoding.encodeList, *]

omit [Fact p.Prime] in
theorem encoded_caches (t theta : Code p μ) (N : ℕ)
    (rows : List (List (List (Code p μ)))) :
    SubexpTaylorCacheControl.encodeCache SubexpTaylorRow.flat (caches p μ M t theta N rows) =
      Encoding.encodeList (incidenceCacheBytes p μ M t theta N) rows := by
  unfold SubexpTaylorCacheControl.encodeCache caches
  rw [encodeList_map_eq]
  congr 1
  funext coordinates
  exact encodeList_map_eq _ _ coordinates

/-- The complete fixed program copies the reusable row master, traverses
incidences and coordinates in their supplied order, and returns the nested
Taylor cache on 102. Every other stack is restored exactly. -/
theorem program_trace (hμ : 0 < μ) (t theta : Code p μ)
    (width blockWidth : List Bool) (hw : width.length = baseWidth p μ)
    (hblock : blockWidth.length = 4 * baseWidth p μ) (N C R : ℕ)
    (rows : List (List (List (Code p μ))))
    (hC : ∀ coordinates ∈ rows, coordinates.length ≤ C)
    (hR : ∀ coordinates ∈ rows, ∀ P ∈ coordinates, P.length ≤ R)
    (d : Data)
    (hi : incidenceInvariant (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) N d)
    (hm : d.stacks 100 = SubexpTaylorCacheControl.encodeRows SubexpTaylorRow.flat rows)
    (h102 : d.stacks 102 = []) (h103 : d.stacks 103 = [])
    (h104 : d.stacks 104 = []) (h108 : d.stacks 108 = []) :
    ∃ n ≤ tableBudget rows.length C R N (baseWidth p μ), ∃ regs : Fin 14 → Bool,
      Trace SubexpTaylorCacheControl.program n
        (d.withPC (some SubexpTaylorCacheControl.program.entry))
        ((⟨regs, Function.update d.stacks 102
          (SubexpTaylorCacheControl.encodeCache SubexpTaylorRow.flat
            (caches p μ M t theta N rows))⟩ : Data).withPC none) := by
  let a := afterCopy d 100 103 0 1
  have hcopy := copy_eval d 100 103 0 0 1 (by decide) (by decide) (by decide) (by decide)
    (clean_0 _ d hi.1.1)
  have ha : incidenceInvariant (SubexpHornerMachine.baseWords p μ M t theta width blockWidth) N a := by
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro i
      have hne := rowStacks_ne_high i (103 : Fin 112) (by decide)
      simpa [a, afterCopy, StackRoutines.copyStacks, hne] using hi.1.1 i
    · simpa [a, afterCopy, StackRoutines.copyStacks] using hi.1.2.1
    · simpa [a, afterCopy, StackRoutines.copyStacks] using hi.1.2.2.1
    · simpa [a, afterCopy, StackRoutines.copyStacks] using hi.1.2.2.2
    · simpa [a, afterCopy, StackRoutines.copyStacks] using hi.2.1
    · simpa [a, afterCopy, StackRoutines.copyStacks] using hi.2.2.1
    · simpa [a, afterCopy, StackRoutines.copyStacks] using hi.2.2.2
  have ha103 : a.stacks 103 = Encoding.encodeList (incidenceBytes p μ) rows := by
    change a.stacks 103 = SubexpTaylorCacheControl.encodeRows SubexpTaylorRow.flat rows
    simpa [a, afterCopy, StackRoutines.copyStacks, h103] using hm
  have ha104 : a.stacks 104 = [] := by
    simpa [a, afterCopy, StackRoutines.copyStacks] using h104
  have ha108 : a.stacks 108 = [] := by
    simpa [a, afterCopy, StackRoutines.copyStacks] using h108
  obtain ⟨ni, hni, b, _, hbs, hr⟩ := incidence_iterations p μ M hμ t theta
    width blockWidth hw hblock N C R rows hC hR a ha ha103 ha104 ha108
  have hfinish := finishList_eval 108 102 (by decide) b
  let final := finishResult 108 102 b
  let output := Encoding.encodeList (incidenceCacheBytes p μ M t theta N) rows
  have hencode : output =
      recordStream (rows.map (incidenceCacheBytes p μ M t theta N)) ++ [false] := by
    change Encoding.encodeList (incidenceCacheBytes p μ M t theta N) rows = _
    rw [← SubexpTaylorRow.encode_map, encodeList_recordStream]
  have hfs : final.stacks = Function.update d.stacks 102 output := by
    funext i
    by_cases h103' : i = 103 <;> by_cases h108' : i = 108 <;> by_cases h102' : i = 102 <;>
      simp [final, finishResult, hbs, a, afterCopy, StackRoutines.copyStacks,
        h103', h108', h102', h102, h103, h108, hencode]
  have hinlen : (d.stacks 100).length ≤
      1 + (2 * incidenceInputBound C R (baseWidth p μ) + 2) * rows.length := by
    rw [hm]
    apply Encoding.length_encodeList_upper
    intro coordinates hc
    apply (incidenceBytes_length_le p μ R coordinates (hR coordinates hc)).trans
    unfold incidenceInputBound
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (hC coordinates hc)) 1
  have houtlen : (b.stacks 108).length ≤
      rows.length * (2 * incidenceOutputBound C N (baseWidth p μ) + 2) := by
    rw [hbs]
    simp only [Function.update_self, List.length_reverse]
    apply mapped_stream_length_le
    intro coordinates hc
    rw [incidenceCacheBytes_length]
    unfold incidenceOutputBound
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (hC coordinates hc)) 1
  refine ⟨(7 * (d.stacks 100).length + 5) + (ni + (3 * (b.stacks 108).length + 8)) + 1,
    ?_, final.regs, ?_⟩
  · unfold tableBudget
    omega
  · have he := hcopy.seq (hr.seq hfinish)
    have hf : final = ⟨final.regs, Function.update d.stacks 102 output⟩ := state_ext rfl hfs
    have ht := compiled_halt_trace he 100 102
    change Trace _ _ _ (final.withPC none) at ht
    rw [hf] at ht
    simpa only [SubexpTaylorCacheControl.program, SubexpTaylorCacheControl.command,
      output, encoded_caches] using ht

end SubexponentialSAT.SubexpTaylorCacheMap

end OAI.Algorithms
