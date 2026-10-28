import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOriginMapCoordinates

namespace OAI.Algorithms

/-! The complete measured incidence/coordinate origin-cache traversal. -/

namespace SubexponentialSAT.SubexpOriginMap

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing SubexpOriginControl SubexpOriginCalls
open SubexpTaylorCacheCalls (recordStream encodeList_recordStream unread_false)

attribute [local simp] Fin.coe_ofNat_eq_mod

def incidenceInvariant (modulus inputWidth width : List Bool) (d : Data) : Prop :=
  clean modulus inputWidth width d ∧ d.stacks 17 = [] ∧ d.stacks 18 = [] ∧
    d.stacks 21 = [] ∧ d.stacks 22 = []

theorem clean_transfer_inner (modulus inputWidth width : List Bool) (d : Data)
    (h : clean modulus inputWidth width d) :
    clean modulus inputWidth width (afterTransfer d 16 17 0 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa [afterTransfer, StackRoutines.transferStacks,
      lowPort_ne_high i 16 (by decide), lowPort_ne_high i 17 (by decide)] using h.1 i
  · simpa [afterTransfer, StackRoutines.transferStacks] using h.2.1
  · simpa [afterTransfer, StackRoutines.transferStacks] using h.2.2.1
  · simpa [afterTransfer, StackRoutines.transferStacks] using h.2.2.2.1
  · simpa [afterTransfer, StackRoutines.transferStacks] using h.2.2.2.2

theorem incidenceInvariant_state (modulus inputWidth width : List Bool) (d : Data)
    (h : incidenceInvariant modulus inputWidth width d) (v pr f : Bool)
    (tail payload : List Bool) :
    incidenceInvariant modulus inputWidth width
      (RecordPrograms.state incidencePorts d v pr f tail payload) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa [RecordPrograms.state, incidencePorts,
      lowPort_ne_high i 15 (by decide), lowPort_ne_high i 16 (by decide)] using h.1.1 i
  · simpa [RecordPrograms.state, incidencePorts] using h.1.2.1
  · simpa [RecordPrograms.state, incidencePorts] using h.1.2.2.1
  · simpa [RecordPrograms.state, incidencePorts] using h.1.2.2.2.1
  · simpa [RecordPrograms.state, incidencePorts] using h.1.2.2.2.2
  · simpa [RecordPrograms.state, incidencePorts] using h.2.1
  · simpa [RecordPrograms.state, incidencePorts] using h.2.2.1
  · simpa [RecordPrograms.state, incidencePorts] using h.2.2.2.1
  · simpa [RecordPrograms.state, incidencePorts] using h.2.2.2.2

variable (p : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)
variable (width : List Bool) (hw : width.length = baseWidth p 1)

theorem incidence_eval {B : ℕ} (hBpos : 0 < B) (inputWidth : List Bool)
    (hB : inputWidth.length = B) (R : ℕ) (rows : List (Row B))
    (hR : ∀ row ∈ rows, row.2.length ≤ R) (d : Data)
    (hi : incidenceInvariant M.bits inputWidth width d)
    (hin : d.stacks 16 = (incidenceBytes rows).reverse) :
    ∃ n ≤ incidenceBound rows.length B (baseWidth p 1) M.bits.length R,
      ∃ regs : Fin 14 → Bool, (∀ i : Fin 14, 11 ≤ i.val → regs i = d.regs i) ∧
      Eval incidenceCallback n d
        ⟨regs, Function.update (Function.update d.stacks 16 []) 23
          ((SubexpTaylorFrames.recordBytes (incidenceOutput p M width hw rows)).reverse ++
            d.stacks 23)⟩ := by
  let a := afterTransfer d 16 17 0 1
  have h1 := transfer_eval d 16 17 0 1 (by decide) (by decide)
  have ha := clean_transfer_inner _ _ _ d hi.1
  have ha17 : a.stacks 17 = incidenceBytes rows := by
    simp [a, afterTransfer, StackRoutines.transferStacks, hin, hi.2.1]
  have ha18 : a.stacks 18 = [] := by
    simpa [a, afterTransfer, StackRoutines.transferStacks] using hi.2.2.1
  have ha21 : a.stacks 21 = [] := by
    simpa [a, afterTransfer, StackRoutines.transferStacks] using hi.2.2.2.1
  have ha22 : a.stacks 22 = [] := by
    simpa [a, afterTransfer, StackRoutines.transferStacks] using hi.2.2.2.2
  obtain ⟨nc, hnc, b, hb, hbs, hbr, h2⟩ := coordinates_eval p M width hw hBpos
    inputWidth hB R rows hR a ha ha17 ha18 ha21 ha22
  let out := incidenceOutput p M width hw rows
  let c := afterTransfer b 22 25 0 1
  let e := writerResult c
  let f := afterTransfer e 26 23 0 1
  have h3 := transfer_eval b 22 25 0 1 (by decide) (by decide)
  have h4 := writeRecord_eval c
  have h5 := transfer_eval e 26 23 0 1 (by decide) (by decide)
  have hb22 : b.stacks 22 = out := by simp [hbs, out]
  have hc25 : c.stacks 25 = out.reverse := by
    simp [c, afterTransfer, StackRoutines.transferStacks, hb22, hb.2.2.2.1]
  have hc26 : c.stacks 26 = [] := by
    simpa [c, afterTransfer, StackRoutines.transferStacks] using hb.2.2.2.2
  have he26 : e.stacks 26 = recordBytes out := by
    simp only [e, writerResult, Function.update_self, hc25,
      List.reverse_reverse, hc26, List.append_nil]
  have hfs : f.stacks = Function.update (Function.update d.stacks 16 []) 23
      ((SubexpTaylorFrames.recordBytes out).reverse ++ d.stacks 23) := by
    funext i
    by_cases h16 : i = 16
    · subst i
      simp [f, e, c, writerResult, afterTransfer, StackRoutines.transferStacks, hbs, a]
    by_cases h17 : i = 17
    · subst i
      simp [f, e, c, writerResult, afterTransfer, StackRoutines.transferStacks, hbs, a, hi.2.1]
    by_cases h22 : i = 22
    · subst i
      simp [f, e, c, writerResult, afterTransfer, StackRoutines.transferStacks, hbs, a, hi.2.2.2.2]
    by_cases h23 : i = 23
    · subst i
      simp [f, e, c, writerResult, afterTransfer, StackRoutines.transferStacks, hbs, a, out,
        hi.1.2.2.2.1, hi.1.2.2.2.2, recordBytes, SubexpTaylorFrames.recordBytes]
    by_cases h25 : i = 25
    · subst i
      simp [f, e, c, writerResult, afterTransfer, StackRoutines.transferStacks, hbs, a, hi.1.2.2.2.1]
    by_cases h26 : i = 26
    · subst i
      simp [f, e, c, writerResult, afterTransfer, StackRoutines.transferStacks, hbs, a, hi.1.2.2.2.2]
    simp [f, e, c, writerResult, afterTransfer, StackRoutines.transferStacks,
      hbs, a, h16, h17, h22, h23, h25, h26]
  refine ⟨(3 * (d.stacks 16).length + 3) +
    (nc + ((3 * (b.stacks 22).length + 3) +
      ((5 * (c.stacks 25).length + 7) + (3 * (e.stacks 26).length + 3)))),
    ?_, f.regs, ?_, ?_⟩
  · have hinlen := incidenceBytes_length_le rows hR
    have houtlen := incidenceOutput_length p M width hw rows
    rw [hin, List.length_reverse, hb22, hc25, List.length_reverse, he26]
    simp only [recordBytes, List.length_cons, Encoding.length_frame]
    change out.length = _ at houtlen
    rw [houtlen]
    unfold incidenceBound
    omega
  · intro i h11
    have h0 : i ≠ 0 := by intro h; subst i; norm_num at h11
    have h1' : i ≠ 1 := by intro h; subst i; norm_num at h11
    have hf : f.regs i = b.regs i := by
      simp [f, e, c, afterTransfer, writerResult, readRegs, h0, h1']
    exact hf.trans ((hbr i h11).trans (readRegs_high d.regs i (by omega)))
  · have hf : f = ⟨f.regs, Function.update (Function.update d.stacks 16 []) 23
        ((SubexpTaylorFrames.recordBytes out).reverse ++ d.stacks 23)⟩ := state_ext rfl hfs
    have he := h1.seq (h2.seq (h3.seq (h4.seq h5)))
    change Eval incidenceCallback _ d f at he
    rw [hf] at he
    exact he

def incidenceEffect {B : ℕ} (bits : List Bool) (a b : Data) : Prop :=
  (∀ rows : List (Row B), incidenceBytes rows = bits → b.stacks 23 =
    (SubexpTaylorFrames.recordBytes (incidenceOutput p M width hw rows)).reverse ++ a.stacks 23) ∧
  (∀ i : Fin 32, i ≠ 15 → i ≠ 16 → i ≠ 23 → b.stacks i = a.stacks i)

def validIncidence (B C R : ℕ) (bits : List Bool) : Prop :=
  ∃ rows : List (Row B), rows.length ≤ C ∧
    (∀ row ∈ rows, row.2.length ≤ R) ∧ incidenceBytes rows = bits

theorem incidence_contract {B : ℕ} (hBpos : 0 < B) (inputWidth : List Bool)
    (hB : inputWidth.length = B) (C R : ℕ) :
    RecordPrograms.CallbackContractWithOn incidencePorts incidenceCallback (fun _ => false)
      (fun _ => incidenceBound C B (baseWidth p 1) M.bits.length R)
      (incidenceInvariant M.bits inputWidth width)
      (incidenceEffect p M width hw (B := B)) (validIncidence B C R) := by
  intro bits tail before hv hi
  obtain ⟨rows, hC, hR, rfl⟩ := hv
  let d := RecordPrograms.state incidencePorts before false true false tail (incidenceBytes rows).reverse
  have hd := incidenceInvariant_state _ _ _ before hi false true false tail (incidenceBytes rows).reverse
  obtain ⟨n, hn, regs, hregs, hr⟩ := incidence_eval p M width hw hBpos inputWidth hB R rows hR
    d hd (RecordPrograms.state_payload _ _ _ _ _ _ _)
  let next : Data := ⟨regs, Function.update (Function.update d.stacks 16 []) 23
    ((SubexpTaylorFrames.recordBytes (incidenceOutput p M width hw rows)).reverse ++ d.stacks 23)⟩
  have hnext : incidenceInvariant M.bits inputWidth width next := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact clean_reg_change _ _ _ _ regs
        (clean_update _ _ _ _ (clean_update _ _ _ d hd.1 16 (by decide) (by decide)
          (by decide) (by decide) (by decide) []) 23 (by decide) (by decide)
          (by decide) (by decide) (by decide) _)
    · simpa [next] using hd.2.1
    · simpa [next] using hd.2.2.1
    · simpa [next] using hd.2.2.2.1
    · simpa [next] using hd.2.2.2.2
  have hfinish : RecordPrograms.state incidencePorts next false true false tail [] = next := by
    apply RecordPrograms.state_eq_self
    · exact (hregs 11 (by decide)).trans (RecordPrograms.state_tag incidencePorts before _ _ _ _ _)
    · exact (hregs 12 (by decide)).trans (RecordPrograms.state_present incidencePorts before _ _ _ _ _)
    · exact (hregs 13 (by decide)).trans (RecordPrograms.state_found incidencePorts before _ _ _ _ _)
    · simp [next, d, RecordPrograms.state, incidencePorts]
    · simp [next, incidencePorts]
  refine ⟨n, next, hn.trans (incidenceBound_mono hC B _ _ R), hnext, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro other hother
      have heq := Encoding.encodeList_injective (rowBytes_injective hBpos) hother
      subst other
      simp [next, d, RecordPrograms.state, incidencePorts]
    · intro i h15 h16 h23
      simp [next, d, RecordPrograms.state, incidencePorts, h15, h16, h23]
  · rw [hfinish]
    exact hr

theorem incidence_iterations {B : ℕ} (hBpos : 0 < B) (inputWidth : List Bool)
    (hB : inputWidth.length = B) (C R : ℕ) (rows : List (List (Row B)))
    (hC : ∀ coordinates ∈ rows, coordinates.length ≤ C)
    (hR : ∀ coordinates ∈ rows, ∀ row ∈ coordinates, row.2.length ≤ R)
    (d : Data) (hi : incidenceInvariant M.bits inputWidth width d)
    (hs : d.stacks 15 = Encoding.encodeList incidenceBytes rows)
    (hp : d.stacks 16 = []) (ha : d.stacks 23 = []) :
    ∃ n ≤ iterationsBound rows.length C B (baseWidth p 1) M.bits.length R,
      ∃ next : Data, incidenceInvariant M.bits inputWidth width next ∧
      next.stacks = Function.update (Function.update d.stacks 15 []) 23
        (recordStream (rows.map (incidenceOutput p M width hw))).reverse ∧
      Eval (RecordPrograms.iterate incidencePorts incidenceCallback) n d next := by
  have hv : ∀ bits ∈ rows.map incidenceBytes, validIncidence B C R bits := by
    intro bits h
    obtain ⟨coordinates, hc, rfl⟩ := List.mem_map.mp h
    exact ⟨coordinates, hC coordinates hc, hR coordinates hc, rfl⟩
  obtain ⟨n, next, hn, hnext, hvisit, hrun⟩ := RecordPrograms.iterate_run_with_on
    incidencePorts incidenceCallback (fun _ => false)
    (fun _ => incidenceBound C B (baseWidth p 1) M.bits.length R)
    (incidenceInvariant M.bits inputWidth width) (incidenceEffect p M width hw (B := B))
    (validIncidence B C R) (incidence_contract p M width hw hBpos inputWidth hB C R)
    (rows.map incidenceBytes) [] d hv hi (d.regs 11) (d.regs 12) (d.regs 13)
  have hstart : RecordPrograms.state incidencePorts d (d.regs 11) (d.regs 12) (d.regs 13)
      (Encoding.encodeList id (rows.map incidenceBytes) ++ []) [] = d := by
    apply RecordPrograms.state_eq_self <;> try rfl
    · change d.stacks 15 = Encoding.encodeList id (rows.map incidenceBytes) ++ []
      simpa only [List.append_nil, SubexpTaylorRow.encode_map] using hs
    · exact hp
  rw [hstart] at hrun
  have hfalse : (rows.map incidenceBytes).any (fun _ => false) = false := by simp
  rw [hfalse, unread_false] at hrun
  let final := RecordPrograms.state incidencePorts next false true false [] []
  have hfinal := incidenceInvariant_state _ _ _ next hnext false true false [] []
  have hpacked := visits_packed incidenceBytes (incidenceOutput p M width hw) 23
    (incidenceEffect p M width hw (B := B)) (fun _ _ _ h => h.1) rows d next hvisit
  have hframe : ∀ i : Fin 32, i ≠ 15 → i ≠ 16 → i ≠ 23 → next.stacks i = d.stacks i := by
    intro i h15 h16 h23
    exact visits_unchanged (fun a => a.stacks i) (incidenceEffect p M width hw (B := B))
      (fun _ _ _ h => h.2 i h15 h16 h23) _ _ _ hvisit
  have hlength : ∀ coordinates ∈ rows, (incidenceBytes coordinates).length ≤
      incidenceInputBound C B R := by
    intro coordinates hc
    apply (incidenceBytes_length_le coordinates (hR coordinates hc)).trans
    unfold incidenceInputBound
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (hC coordinates hc)) 1
  have hb := SubexpTaylorCacheMap.mapped_budget_le incidenceBytes rows
    (incidenceBound C B (baseWidth p 1) M.bits.length R) (incidenceInputBound C B R) hlength
  refine ⟨n, hn.trans (Nat.add_le_add_left hb 3), final, hfinal, ?_, hrun⟩
  funext i
  by_cases h15 : i = 15
  · subst i; simp [final, RecordPrograms.state, incidencePorts]
  by_cases h16 : i = 16
  · subst i; simp [final, RecordPrograms.state, incidencePorts, hp]
  by_cases h23 : i = 23
  · subst i; simpa [final, RecordPrograms.state, incidencePorts, ha] using hpacked
  · simpa [final, RecordPrograms.state, incidencePorts, h15, h16, h23]
      using hframe i h15 h16 h23

/-- The actual fixed map preserves its Taylor-cache master and changes only
the output stack. No supplied origin list or arithmetic callback occurs. -/
theorem program_trace {B : ℕ} (hBpos : 0 < B) (inputWidth : List Bool)
    (hB : inputWidth.length = B) (C R : ℕ) (rows : List (List (Row B)))
    (hC : ∀ coordinates ∈ rows, coordinates.length ≤ C)
    (hR : ∀ coordinates ∈ rows, ∀ row ∈ coordinates, row.2.length ≤ R)
    (d : Data) (hi : incidenceInvariant M.bits inputWidth width d)
    (hm : d.stacks 14 = inputBytes rows)
    (h15 : d.stacks 15 = []) (h16 : d.stacks 16 = [])
    (h23 : d.stacks 23 = []) (h24 : d.stacks 24 = []) :
    ∃ n ≤ tableBound rows.length C B (baseWidth p 1) M.bits.length R,
      ∃ regs : Fin 14 → Bool, Trace program n
        (d.withPC (some program.entry))
        ((⟨regs, Function.update d.stacks 24 (outputBytes p M width hw rows)⟩ : Data).withPC none) := by
  let a := afterCopy d 14 15 0 1
  have h0 : d.stacks 0 = [] := hi.1.1 0
  have hcopy := copy_eval d 14 15 0 0 1 (by decide) (by decide) (by decide) (by decide) h0
  have ha : incidenceInvariant M.bits inputWidth width a := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro i
        simpa [a, afterCopy, StackRoutines.copyStacks, lowPort_ne_high i 15 (by decide)] using hi.1.1 i
      · simpa [a, afterCopy, StackRoutines.copyStacks] using hi.1.2.1
      · simpa [a, afterCopy, StackRoutines.copyStacks] using hi.1.2.2.1
      · simpa [a, afterCopy, StackRoutines.copyStacks] using hi.1.2.2.2.1
      · simpa [a, afterCopy, StackRoutines.copyStacks] using hi.1.2.2.2.2
    · simpa [a, afterCopy, StackRoutines.copyStacks] using hi.2.1
    · simpa [a, afterCopy, StackRoutines.copyStacks] using hi.2.2.1
    · simpa [a, afterCopy, StackRoutines.copyStacks] using hi.2.2.2.1
    · simpa [a, afterCopy, StackRoutines.copyStacks] using hi.2.2.2.2
  have ha15 : a.stacks 15 = Encoding.encodeList incidenceBytes rows := by
    change a.stacks 15 = inputBytes rows
    simpa [a, afterCopy, StackRoutines.copyStacks, h15] using hm
  have ha16 : a.stacks 16 = [] := by simpa [a, afterCopy, StackRoutines.copyStacks] using h16
  have ha23 : a.stacks 23 = [] := by simpa [a, afterCopy, StackRoutines.copyStacks] using h23
  obtain ⟨ni, hni, b, _, hbs, hr⟩ := incidence_iterations p M width hw hBpos inputWidth hB C R
    rows hC hR a ha ha15 ha16 ha23
  have hfinish := finishList_eval 23 24 (by decide) b
  let final := finishResult 23 24 b
  let output := outputBytes p M width hw rows
  have hencode : output = recordStream (rows.map (incidenceOutput p M width hw)) ++ [false] := by
    change Encoding.encodeList (incidenceOutput p M width hw) rows = _
    rw [← SubexpTaylorRow.encode_map, encodeList_recordStream]
  have hfs : final.stacks = Function.update d.stacks 24 output := by
    funext i
    by_cases h15' : i = 15 <;> by_cases h23' : i = 23 <;> by_cases h24' : i = 24 <;>
      simp [final, finishResult, hbs, a, afterCopy, StackRoutines.copyStacks,
        h15', h23', h24', h15, h23, h24, hencode]
  have hinlen : (d.stacks 14).length ≤
      1 + (2 * incidenceInputBound C B R + 2) * rows.length := by
    rw [hm]
    apply Encoding.length_encodeList_upper
    intro coordinates hc
    apply (incidenceBytes_length_le coordinates (hR coordinates hc)).trans
    unfold incidenceInputBound
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (hC coordinates hc)) 1
  have houtlen : (b.stacks 23).length ≤ rows.length * (2 * incidenceOutputBound C (baseWidth p 1) + 2) := by
    rw [hbs]
    simp only [Function.update_self, List.length_reverse]
    apply SubexpTaylorCacheMap.mapped_stream_length_le
    intro coordinates hc
    rw [incidenceOutput_length]
    unfold incidenceOutputBound
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (hC coordinates hc)) 1
  refine ⟨(7 * (d.stacks 14).length + 5) + (ni + (3 * (b.stacks 23).length + 8)) + 1,
    ?_, final.regs, ?_⟩
  · unfold tableBound
    omega
  · have he := hcopy.seq (hr.seq hfinish)
    have hf : final = ⟨final.regs, Function.update d.stacks 24 output⟩ := state_ext rfl hfs
    have ht := compiled_halt_trace he 14 24
    change Trace _ _ _ (final.withPC none) at ht
    rw [hf] at ht
    exact ht

theorem program_runsIn {B : ℕ} (hBpos : 0 < B) (inputWidth : List Bool)
    (hB : inputWidth.length = B) (C R : ℕ) (rows : List (List (Row B)))
    (hC : ∀ coordinates ∈ rows, coordinates.length ≤ C)
    (hR : ∀ coordinates ∈ rows, ∀ row ∈ coordinates, row.2.length ≤ R)
    (d : Data) (hi : incidenceInvariant M.bits inputWidth width d)
    (hm : d.stacks 14 = inputBytes rows)
    (h15 : d.stacks 15 = []) (h16 : d.stacks 16 = [])
    (h23 : d.stacks 23 = []) (h24 : d.stacks 24 = []) :
    ∃ regs : Fin 14 → Bool,
      RunsIn program (tableBound rows.length C B (baseWidth p 1) M.bits.length R)
        (d.withPC (some program.entry))
        ((⟨regs, Function.update d.stacks 24 (outputBytes p M width hw rows)⟩ : Data).withPC none) := by
  obtain ⟨n, hn, regs, ht⟩ := program_trace p M width hw hBpos inputWidth hB C R rows hC hR
    d hi hm h15 h16 h23 h24
  exact ⟨regs, n, hn, ht⟩

def polynomialBound (W : ℕ) : ℕ := tableBound W W W W W W

theorem tableBound_le {I C B b m R W : ℕ}
    (hI : I ≤ W) (hC : C ≤ W) (hB : B ≤ W) (hb : b ≤ W) (hm : m ≤ W) (hR : R ≤ W) :
    tableBound I C B b m R ≤ polynomialBound W := by
  unfold polynomialBound tableBound iterationsBound incidenceBound incidenceInputBound
    incidenceOutputBound coordinatesBound coordinateBound rowBound tailBound
    SubexpOriginQuadProgram.cost SubexpFlatLift.wordCost SubexpWordLiftMachine.runtimeBound
  gcongr

end SubexponentialSAT.SubexpOriginMap

end OAI.Algorithms
