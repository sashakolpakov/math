import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOriginMapData
import OAI.Algorithms.SubexponentialSAT.SubexpOriginCalls

namespace OAI.Algorithms

/-! Actual coordinate traversal for the origin cache. -/

namespace SubexponentialSAT.SubexpOriginMap

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing SubexpOriginControl SubexpOriginCalls
open SubexpTaylorCacheCalls (recordStream encodeList_recordStream unread_false)

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem lowPort_ne_high (i : Fin 14) (j : Fin 32) (hj : 14 ≤ j.val) : lowPort i ≠ j := by
  intro he
  have hv := congrArg Fin.val he
  change i.val = j.val at hv
  omega

theorem clean_reg_change (modulus inputWidth width : List Bool) (d : Data)
    (regs : Fin 14 → Bool) (h : clean modulus inputWidth width d) :
    clean modulus inputWidth width ⟨regs, d.stacks⟩ := h

theorem clean_update (modulus inputWidth width : List Bool) (d : Data)
    (h : clean modulus inputWidth width d) (j : Fin 32) (hj : 14 ≤ j.val)
    (h19 : j ≠ 19) (h20 : j ≠ 20) (h25 : j ≠ 25) (h26 : j ≠ 26) (bits : List Bool) :
    clean modulus inputWidth width ⟨d.regs, Function.update d.stacks j bits⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [Function.update_of_ne (lowPort_ne_high i j hj)] using h.1 i
  · simpa only [Function.update_of_ne h19.symm] using h.2.1
  · simpa only [Function.update_of_ne h20.symm] using h.2.2.1
  · simpa only [Function.update_of_ne h25.symm] using h.2.2.2.1
  · simpa only [Function.update_of_ne h26.symm] using h.2.2.2.2

theorem clean_coordinate_state (modulus inputWidth width : List Bool) (d : Data)
    (h : clean modulus inputWidth width d) (v pr f : Bool) (tail payload : List Bool) :
    clean modulus inputWidth width (RecordPrograms.state coordinatePorts d v pr f tail payload) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [RecordPrograms.state, coordinatePorts,
      Function.update_of_ne (lowPort_ne_high i 18 (by decide)),
      Function.update_of_ne (lowPort_ne_high i 17 (by decide))] using h.1 i
  · simpa [RecordPrograms.state, coordinatePorts] using h.2.1
  · simpa [RecordPrograms.state, coordinatePorts] using h.2.2.1
  · simpa [RecordPrograms.state, coordinatePorts] using h.2.2.2.1
  · simpa [RecordPrograms.state, coordinatePorts] using h.2.2.2.2

theorem coordinateCost_le {B R : ℕ} (row : Row B) (hr : row.2.length ≤ R) (b m : ℕ) :
    coordinateCost B b m row ≤ coordinateBound B b m R := by
  have hrow := rowBytes_length_le row hr
  have htail : (Encoding.encodeList SubexpFlatLift.encode row.2).length ≤ tailBound B R := by
    rw [degreeBytes_length]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hr) 1
  unfold coordinateCost coordinateBound
  omega

variable (p : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)
variable (width : List Bool) (hw : width.length = baseWidth p 1)

def coordinateEffect {B : ℕ} (bits : List Bool) (a b : Data) : Prop :=
  (∀ row : Row B, rowBytes row = bits → b.stacks 21 =
    (SubexpTaylorFrames.recordBytes (originBytes p M width hw row)).reverse ++ a.stacks 21) ∧
  (∀ i : Fin 32, i ≠ 17 → i ≠ 18 → i ≠ 21 → b.stacks i = a.stacks i) ∧
  (∀ i : Fin 14, 11 ≤ i.val → b.regs i = a.regs i)

def validRow (B R : ℕ) (bits : List Bool) : Prop :=
  ∃ row : Row B, row.2.length ≤ R ∧ rowBytes row = bits

theorem coordinate_contract {B : ℕ} (hBpos : 0 < B) (inputWidth : List Bool)
    (hB : inputWidth.length = B) (R : ℕ) :
    RecordPrograms.CallbackContractWithOn coordinatePorts coordinateCallback (fun _ => false)
      (fun _ => coordinateBound B (baseWidth p 1) M.bits.length R)
      (clean M.bits inputWidth width) (coordinateEffect p M width hw (B := B)) (validRow B R) := by
  intro bits tail before hv hi
  obtain ⟨row, hrow, rfl⟩ := hv
  let d := RecordPrograms.state coordinatePorts before false true false tail (rowBytes row).reverse
  have hd := clean_coordinate_state M.bits inputWidth width before hi false true false tail
    (rowBytes row).reverse
  obtain ⟨n, hn, regs, hregs, hr⟩ := coordinate_eval p M width hw row inputWidth hB d hd
    (RecordPrograms.state_payload _ _ _ _ _ _ _)
  let next : Data := ⟨regs, Function.update (Function.update d.stacks 18 []) 21
    ((SubexpTaylorFrames.recordBytes (originBytes p M width hw row)).reverse ++ d.stacks 21)⟩
  have hnext : clean M.bits inputWidth width next := by
    exact clean_reg_change _ _ _ _ regs
      (clean_update _ _ _ _ (clean_update _ _ _ d hd 18 (by decide) (by decide)
        (by decide) (by decide) (by decide) []) 21 (by decide) (by decide)
        (by decide) (by decide) (by decide) _)
  have hfinish : RecordPrograms.state coordinatePorts next false true false tail [] = next := by
    apply RecordPrograms.state_eq_self
    · exact (hregs 8 (by decide)).trans (RecordPrograms.state_tag coordinatePorts before _ _ _ _ _)
    · exact (hregs 9 (by decide)).trans (RecordPrograms.state_present coordinatePorts before _ _ _ _ _)
    · exact (hregs 10 (by decide)).trans (RecordPrograms.state_found coordinatePorts before _ _ _ _ _)
    · simp [next, d, RecordPrograms.state, coordinatePorts]
    · simp [next, coordinatePorts]
  refine ⟨n, next, hn.trans (coordinateCost_le row hrow _ _), hnext, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro other he
      have heq := rowBytes_injective hBpos he
      subst other
      simp [next, d, RecordPrograms.state, coordinatePorts]
    · intro i h17 h18 h21
      simp [next, d, RecordPrograms.state, coordinatePorts, h17, h18, h21]
    · intro i h11
      change regs i = before.regs i
      rw [hregs i (by omega)]
      have h8 : i ≠ 8 := by intro h; subst i; norm_num at h11
      have h9 : i ≠ 9 := by intro h; subst i; norm_num at h11
      have h10 : i ≠ 10 := by intro h; subst i; norm_num at h11
      simp [d, RecordPrograms.state, coordinatePorts, h8, h9, h10]
  · rw [hfinish]
    exact hr

theorem coordinate_iterations {B : ℕ} (hBpos : 0 < B) (inputWidth : List Bool)
    (hB : inputWidth.length = B) (R : ℕ) (rows : List (Row B))
    (hR : ∀ row ∈ rows, row.2.length ≤ R) (d : Data)
    (hi : clean M.bits inputWidth width d)
    (hs : d.stacks 17 = Encoding.encodeList rowBytes rows)
    (hp : d.stacks 18 = []) (ha : d.stacks 21 = []) :
    ∃ n ≤ 3 + rows.length * (6 * rowBound B R + coordinateBound B (baseWidth p 1) M.bits.length R + 7),
      ∃ next : Data, clean M.bits inputWidth width next ∧
      next.stacks = Function.update (Function.update d.stacks 17 []) 21
        (recordStream (rows.map (originBytes p M width hw))).reverse ∧
      (∀ i : Fin 14, 11 ≤ i.val → next.regs i = d.regs i) ∧
      Eval (RecordPrograms.iterate coordinatePorts coordinateCallback) n d next := by
  have hv : ∀ bits ∈ rows.map rowBytes, validRow B R bits := by
    intro bits hb
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hb
    exact ⟨row, hR row hr, rfl⟩
  obtain ⟨n, next, hn, hnext, hvisit, hrun⟩ := RecordPrograms.iterate_run_with_on
    coordinatePorts coordinateCallback (fun _ => false)
    (fun _ => coordinateBound B (baseWidth p 1) M.bits.length R)
    (clean M.bits inputWidth width) (coordinateEffect p M width hw (B := B)) (validRow B R)
    (coordinate_contract p M width hw hBpos inputWidth hB R)
    (rows.map rowBytes) [] d hv hi (d.regs 8) (d.regs 9) (d.regs 10)
  have hstart : RecordPrograms.state coordinatePorts d (d.regs 8) (d.regs 9) (d.regs 10)
      (Encoding.encodeList id (rows.map rowBytes) ++ []) [] = d := by
    apply RecordPrograms.state_eq_self <;> try rfl
    · change d.stacks 17 = Encoding.encodeList id (rows.map rowBytes) ++ []
      simpa only [List.append_nil, SubexpTaylorRow.encode_map] using hs
    · exact hp
  rw [hstart] at hrun
  have hfalse : (rows.map rowBytes).any (fun _ => false) = false := by simp
  rw [hfalse, unread_false] at hrun
  let final := RecordPrograms.state coordinatePorts next false true false [] []
  have hfinal := clean_coordinate_state _ _ _ next hnext false true false [] []
  have hpacked := visits_packed rowBytes (originBytes p M width hw) 21
    (coordinateEffect p M width hw (B := B)) (fun _ _ _ h => h.1) rows d next hvisit
  have hframe : ∀ i : Fin 32, i ≠ 17 → i ≠ 18 → i ≠ 21 → next.stacks i = d.stacks i := by
    intro i h17 h18 h21
    exact visits_unchanged (fun a => a.stacks i) (coordinateEffect p M width hw (B := B))
      (fun _ _ _ h => h.2.1 i h17 h18 h21) _ _ _ hvisit
  have hreg : ∀ i : Fin 14, 11 ≤ i.val → next.regs i = d.regs i := by
    intro i hi
    exact visits_unchanged (fun a => a.regs i) (coordinateEffect p M width hw (B := B))
      (fun _ _ _ h => h.2.2 i hi) _ _ _ hvisit
  have hb := SubexpTaylorCacheMap.mapped_budget_le rowBytes rows
    (coordinateBound B (baseWidth p 1) M.bits.length R) (rowBound B R)
    (fun row hr => rowBytes_length_le row (hR row hr))
  refine ⟨n, hn.trans (Nat.add_le_add_left hb 3), final, hfinal, ?_, ?_, hrun⟩
  · funext i
    by_cases h17 : i = 17
    · subst i; simp [final, RecordPrograms.state, coordinatePorts]
    by_cases h18 : i = 18
    · subst i; simp [final, RecordPrograms.state, coordinatePorts, hp]
    by_cases h21 : i = 21
    · subst i; simpa [final, RecordPrograms.state, coordinatePorts, ha] using hpacked
    · simpa [final, RecordPrograms.state, coordinatePorts, h17, h18, h21]
        using hframe i h17 h18 h21
  · intro i h11
    have h8 : i ≠ 8 := by intro h; subst i; norm_num at h11
    have h9 : i ≠ 9 := by intro h; subst i; norm_num at h11
    have h10 : i ≠ 10 := by intro h; subst i; norm_num at h11
    simpa [final, RecordPrograms.state, coordinatePorts, h8, h9, h10] using hreg i h11

theorem coordinates_eval {B : ℕ} (hBpos : 0 < B) (inputWidth : List Bool)
    (hB : inputWidth.length = B) (R : ℕ) (rows : List (Row B))
    (hR : ∀ row ∈ rows, row.2.length ≤ R) (d : Data)
    (hi : clean M.bits inputWidth width d)
    (hs : d.stacks 17 = Encoding.encodeList rowBytes rows)
    (hp : d.stacks 18 = []) (ha : d.stacks 21 = []) (ho : d.stacks 22 = []) :
    ∃ n ≤ coordinatesBound rows.length B (baseWidth p 1) M.bits.length R,
      ∃ next : Data, clean M.bits inputWidth width next ∧
      next.stacks = Function.update (Function.update d.stacks 17 []) 22
        (incidenceOutput p M width hw rows) ∧
      (∀ i : Fin 14, 11 ≤ i.val → next.regs i = d.regs i) ∧
      Eval coordinates n d next := by
  obtain ⟨n, hn, middle, hm, hms, hmr, hr⟩ := coordinate_iterations p M width hw hBpos
    inputWidth hB R rows hR d hi hs hp ha
  have hf := finishList_eval 21 22 (by decide) middle
  let final := finishResult 21 22 middle
  have hlen : (middle.stacks 21).length = rows.length * (8 * baseWidth p 1 + 2) := by
    rw [hms]
    simp only [Function.update_self, List.length_reverse, origin_stream_length]
  have hout : final.stacks = Function.update (Function.update d.stacks 17 []) 22
      (incidenceOutput p M width hw rows) := by
    have hencode : incidenceOutput p M width hw rows =
        recordStream (rows.map (originBytes p M width hw)) ++ [false] := by
      rw [incidenceOutput, ← SubexpTaylorRow.encode_map, encodeList_recordStream]
    funext i
    by_cases h17 : i = 17 <;> by_cases h21 : i = 21 <;> by_cases h22 : i = 22 <;>
      simp [final, finishResult, hms, h17, h21, h22, ha, ho, hencode]
  have hi' : clean M.bits inputWidth width final := by
    have hc := clean_update _ _ _ _ (clean_update _ _ _ d hi 17 (by decide) (by decide)
      (by decide) (by decide) (by decide) []) 22 (by decide) (by decide)
      (by decide) (by decide) (by decide) (incidenceOutput p M width hw rows)
    rw [show final = ⟨final.regs, Function.update (Function.update d.stacks 17 []) 22
      (incidenceOutput p M width hw rows)⟩ from state_ext rfl hout]
    exact clean_reg_change _ _ _ _ final.regs hc
  refine ⟨n + (3 * (middle.stacks 21).length + 8), ?_, final, hi', hout, ?_, hr.seq hf⟩
  · rw [hlen]
    unfold coordinatesBound
    omega
  · intro i h11
    exact (readRegs_high middle.regs i (by omega)).trans (hmr i h11)

end SubexponentialSAT.SubexpOriginMap

end OAI.Algorithms
