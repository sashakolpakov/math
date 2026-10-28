import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNativeSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.MomentsAssemblyFoldRel
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

/-! Relational execution of the fixed specialized factor-record loop. This
adapts the original FactorLoop reader/while proof to the shared 896-stack ABI
and empty-support dictionaries. The explicit callback premise must be proved
for the actual callback before this component can close an algorithm endpoint. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop
attribute [local simp] Fin.coe_ofNat_eq_mod
open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram MomentsProgram

abbrev Raw (n B d : ℕ) := List (Product.Entry n B d)

def state {n B d : ℕ} (base : Fin 896 → List Bool) (regs : Fin 40 → Bool)
    (seed : Raw n B d) (source payload : List Bool) : FactorAssignmentProgram.Data :=
  ⟨regs,Function.update (Function.update (Function.update base 151 (Product.bytes seed))
    150 source) 149 payload⟩

def recordState {n B d : ℕ} (base : Fin 896 → List Bool) (regs : Fin 40 → Bool)
    (seed : Raw n B d) (v pr f : Bool) (source payload : List Bool) : FactorAssignmentProgram.Data :=
  RecordPrograms.state FactorAssignmentProgram.ports (state base regs seed [] []) v pr f source payload

def records (ids : List ℕ) : List (List Bool) := ids.map Encoding.encodeNat

def loopBudget (C : ℕ) (ids : List ℕ) : ℕ :=
  RecordPrograms.budget (fun _ => C) (records ids)+3

theorem recordState_eq {n B d : ℕ} (base : Fin 896 → List Bool)
    (regs : Fin 40 → Bool) (seed : Raw n B d) (v pr f : Bool) (source payload : List Bool) :
    recordState base regs seed v pr f source payload =
      state base (recordState base regs seed v pr f source payload).regs seed source payload := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    by_cases h149 : i=149 <;> by_cases h150 : i=150 <;>
      simp [FactorAssignmentProgram.ports, state, Function.update_apply, h149, h150]

theorem recordState_self {n B d : ℕ} (base : Fin 896 → List Bool)
    (regs : Fin 40 → Bool) (seed : Raw n B d) (v pr f : Bool) (source payload : List Bool)
    (h13 : regs 13=v) (h14 : regs 14=pr) (h15 : regs 15=f) :
    recordState base regs seed v pr f source payload = state base regs seed source payload := by
  rw [recordState_eq]
  congr 1
  funext i
  by_cases h1 : i=13 <;> by_cases h2 : i=14 <;> by_cases h3 : i=15 <;>
    simp_all [recordState, RecordPrograms.state, FactorAssignmentProgram.ports, state]

theorem inner_eval {n B d : ℕ} (u J : ℕ)
    (step : Raw n B d → ℕ → Raw n B d → Prop)
    (ready : (Fin 896 → List Bool) → Prop) (eligible : ℕ → Prop) (T C : ℕ)
    (contract : ∀ base, ready base → ∀ id seed tail regs, eligible id →
      NativeSemantics.Good ∅ u J seed → tail.length ≤ T →
      ∃ out, NativeSemantics.Good ∅ u J out ∧ step seed id out ∧
        ∃ k ≤ C, ∃ rr,
          Eval FactorAssignmentProgram.callback k
            (state base regs seed tail (Encoding.encodeNat id).reverse)
            (state base rr out tail []) ∧ rr 13 = false ∧ rr 14 = true ∧ rr 15 = false)
    (base : Fin 896 → List Bool) (hb : ready base)
    (ids : List ℕ) (seed : Raw n B d) (regs : Fin 40 → Bool)
    (hg : NativeSemantics.Good ∅ u J seed) (hids : ∀ id ∈ ids, eligible id)
    (hlen : (ProgramEncoding.encodeRecords (records ids)).length ≤ T) :
    ∃ out, NativeSemantics.Good ∅ u J out ∧ MomentsAssembly.Relational.FoldRel step ids seed out ∧
      ∃ k ≤ 1+RecordPrograms.budget (fun _ => C) (records ids), ∃ rr,
        Eval (RecordPrograms.loop FactorAssignmentProgram.ports FactorAssignmentProgram.callback) k
          (RecordPrograms.afterTag FactorAssignmentProgram.ports (state base regs seed [] []) (records ids) [])
          (recordState base rr out false true false [] []) := by
  induction ids generalizing seed regs with
  | nil =>
    refine ⟨seed,hg,.nil seed,1,by simp [records,RecordPrograms.budget],regs,?_⟩
    apply Eval.while_false
    simp [RecordPrograms.afterTag,records,FactorAssignmentProgram.ports,RecordPrograms.state]
  | cons fid ids ih =>
    let bits := Encoding.encodeNat fid
    let tail := Encoding.encodeList id (records ids) ++ []
    let parsed := recordState base regs seed false true false tail bits.reverse
    obtain ⟨next,hnext,hstep,k,hk,rr,hcall,h13,h14,h15⟩ :=
      contract base hb fid seed tail parsed.regs (hids fid (by simp)) hg (by
        have hh : (ProgramEncoding.encodeRecords (records ids)).length ≤ T := by
          simp only [ProgramEncoding.encodeRecords,records,List.map_cons,Encoding.encodeList,
            List.length_cons,List.length_append] at hlen ⊢
          omega
        simpa [tail,ProgramEncoding.encodeRecords] using hh)
    have hcall' : Eval FactorAssignmentProgram.callback k parsed
        (recordState base rr next false true false tail []) := by
      rw [recordState_self base rr next false true false tail [] h13 h14 h15]
      have hp : parsed = state base parsed.regs seed tail bits.reverse :=
        recordState_eq base regs seed false true false tail bits.reverse
      rw [hp]
      exact hcall
    have hreader : Eval (RecordPrograms.reader FactorAssignmentProgram.ports) (6*bits.length+4)
        (RecordPrograms.afterTag FactorAssignmentProgram.ports (state base regs seed [] []) (records (fid::ids)) [])
        parsed := by
      simpa [parsed,recordState,records,RecordPrograms.afterTag,bits,tail] using
        RecordPrograms.reader_eval FactorAssignmentProgram.ports (state base regs seed [] []) bits tail [] true true false
    have hbranch : Eval
        (.ite FactorAssignmentProgram.ports.found (RecordPrograms.atom (.set FactorAssignmentProgram.ports.tag false))
          (RecordPrograms.atom (.pop FactorAssignmentProgram.ports.source FactorAssignmentProgram.ports.tag FactorAssignmentProgram.ports.present))) 2
        (recordState base rr next false true false tail [])
        (RecordPrograms.afterTag FactorAssignmentProgram.ports (state base rr next [] []) (records ids) []) := by
      apply Eval.ite_false (by simp [recordState])
      exact RecordPrograms.pop_list_eval FactorAssignmentProgram.ports (state base rr next [] []) (records ids) [] false true
    obtain ⟨out,hout,hrel,m,hm,rf,hrest⟩ := ih next rr hnext (fun id hi => hids id (by simp [hi])) (by
      simp only [ProgramEncoding.encodeRecords,records,List.map_cons,Encoding.encodeList,
        List.length_cons,List.length_append] at hlen ⊢
      omega)
    have hguard :
        (RecordPrograms.afterTag FactorAssignmentProgram.ports (state base regs seed [] []) (records (fid::ids)) []).regs
          FactorAssignmentProgram.ports.tag=true := by simp [RecordPrograms.afterTag,records]
    refine ⟨out,hout,.cons hstep hrel,(6*bits.length+4+(k+2))+m+1,?_,rf,?_⟩
    · simp only [records,List.map_cons,RecordPrograms.budget] at hm ⊢
      dsimp [bits]
      omega
    · exact Eval.while_true hguard (hreader.seq (hcall'.seq hbranch)) hrest

theorem loop_eval {n B d : ℕ} (u J : ℕ)
    (step : Raw n B d → ℕ → Raw n B d → Prop)
    (ready : (Fin 896 → List Bool) → Prop) (eligible : ℕ → Prop) (T C : ℕ)
    (contract : ∀ base, ready base → ∀ id seed tail regs, eligible id →
      NativeSemantics.Good ∅ u J seed → tail.length ≤ T →
      ∃ out, NativeSemantics.Good ∅ u J out ∧ step seed id out ∧
        ∃ k ≤ C, ∃ rr,
          Eval FactorAssignmentProgram.callback k
            (state base regs seed tail (Encoding.encodeNat id).reverse)
            (state base rr out tail []) ∧ rr 13 = false ∧ rr 14 = true ∧ rr 15 = false)
    (base : Fin 896 → List Bool) (hb : ready base)
    (ids : List ℕ) (seed : Raw n B d) (regs : Fin 40 → Bool)
    (hg : NativeSemantics.Good ∅ u J seed) (hids : ∀ id ∈ ids, eligible id)
    (hlen : (ProgramEncoding.encodeRecords (records ids)).length ≤ T) :
    ∃ out, NativeSemantics.Good ∅ u J out ∧ MomentsAssembly.Relational.FoldRel step ids seed out ∧
      ∃ k ≤ loopBudget C ids, ∃ rr,
        Eval FactorAssignmentProgram.loop k
          (state base regs seed (ProgramEncoding.encodeRecords (records ids)) [])
          (state base rr out [] []) := by
  obtain ⟨out,hout,hr,k,hk,rr,he⟩ := inner_eval u J step ready eligible T C contract base hb ids seed regs hg hids hlen
  let initial := state base regs seed (ProgramEncoding.encodeRecords (records ids)) []
  have hstart : recordState base regs seed (regs 13) (regs 14) (regs 15)
      (Encoding.encodeList id (records ids) ++ []) [] = initial := by
    rw [recordState_self base regs seed _ _ _ _ _ rfl rfl rfl]
    simp [initial,ProgramEncoding.encodeRecords]
  have hset := RecordPrograms.set_found_eval FactorAssignmentProgram.ports (state base regs seed [] [])
    (regs 13) (regs 14) (regs 15) false (Encoding.encodeList id (records ids) ++ []) []
  have hpop := RecordPrograms.pop_list_eval FactorAssignmentProgram.ports (state base regs seed [] [])
    (records ids) [] (regs 13) (regs 14)
  have hrun := hset.seq (hpop.seq he)
  change Eval FactorAssignmentProgram.loop (1+(1+k))
    (recordState base regs seed (regs 13) (regs 14) (regs 15) _ [])
    (recordState base rr out false true false [] []) at hrun
  rw [hstart,recordState_eq] at hrun
  exact ⟨out,hout,hr,1+(1+k),by dsimp [loopBudget]; omega,_,hrun⟩

theorem loopBudget_le (C : ℕ) (ids : List ℕ) :
    loopBudget C ids ≤ (C+17)*((ProgramEncoding.encodeRecords (records ids)).length+1) := by
  have h := RecordPrograms.program_budget_le_input (fun _ => C) (records ids) 0 C (by simp)
  simp only [Nat.zero_add] at h
  dsimp [loopBudget]
  omega
def byteBound (n B d u J : ℕ) : ℕ :=
  u * J * (2 * (u + J + n) + 2 * (d * B) + 2)

def productBudget (n B d u J C : ℕ) (ids : List ℕ) : ℕ :=
  7*(ProgramEncoding.encodeRecords (records ids)).length+
    16*byteBound n B d u J+loopBudget C ids+18

theorem product_eval {n B d : ℕ} (u J : ℕ)
    (step : Raw n B d → ℕ → Raw n B d → Prop)
    (ready : (Fin 896 → List Bool) → Prop) (eligible : ℕ → Prop) (T C : ℕ)
    (contract : ∀ base, ready base → ∀ id seed tail regs, eligible id →
      NativeSemantics.Good ∅ u J seed → tail.length ≤ T →
      ∃ out, NativeSemantics.Good ∅ u J out ∧ step seed id out ∧
        ∃ k ≤ C, ∃ rr,
          Eval FactorAssignmentProgram.callback k
            (state base regs seed tail (Encoding.encodeNat id).reverse)
            (state base rr out tail []) ∧ rr 13 = false ∧ rr 14 = true ∧ rr 15 = false)
    (a : FactorAssignmentProgram.Data) (ha : ready a.stacks) (ids : List ℕ) (one : Raw n B d)
    (hg : NativeSemantics.Good ∅ u J one) (hids : ∀ id ∈ ids, eligible id)
    (hlen : (ProgramEncoding.encodeRecords (records ids)).length ≤ T)
    (h175 : a.stacks 175=ProgramEncoding.encodeRecords (records ids))
    (h69 : a.stacks 69=Product.bytes one)
    (h149 : a.stacks 149=[]) (h150 : a.stacks 150=[]) (h151 : a.stacks 151=[])
    (h854 : a.stacks 854=[]) (h159 : a.stacks 159=[]) :
    ∃ out, NativeSemantics.Good ∅ u J out ∧ MomentsAssembly.Relational.FoldRel step ids one out ∧
      ∃ k ≤ productBudget n B d u J C ids, ∃ rr,
        Eval FactorAssignmentProgram.product k a ⟨rr,Function.update a.stacks 854 (Product.bytes out)⟩ := by
  let a1 := SubexpScanPrimitives.afterCopy a 175 150 0 1
  let a2 := SubexpScanPrimitives.afterCopy a1 69 151 0 1
  have h1 : Eval (FactorAssignmentProgram.copy 175 150) (7*(a.stacks 175).length+5) a a1 :=
    SubexpScanPrimitives.copy_eval a 175 150 159 0 1 (by decide) (by decide) (by decide) (by decide) h159
  have h2 : Eval (FactorAssignmentProgram.copy 69 151) (7*(a1.stacks 69).length+5) a1 a2 :=
    SubexpScanPrimitives.copy_eval a1 69 151 159 0 1 (by decide) (by decide) (by decide) (by decide)
      (by simpa [a1,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks] using h159)
  have hinput : a2=state a.stacks a2.regs one (ProgramEncoding.encodeRecords (records ids)) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases h1 : i=149 <;> by_cases h2 : i=150 <;> by_cases h3 : i=151 <;>
        simp_all [a2, a1, SubexpScanPrimitives.afterCopy, StackRoutines.copyStacks, state]
  obtain ⟨out,ho,hr,nl,hl,rr,he⟩ := loop_eval u J step ready eligible T C contract a.stacks ha ids one
    a2.regs hg hids hlen
  rw [← hinput] at he
  let b := state a.stacks rr out [] []
  have h3 := FactorAssignmentProgram.move_eval b 151 854 (by decide) (by decide) (by decide)
    (by simpa [b,state] using h159)
  have hout : FactorAssignmentProgram.moved b 151 854 =
      ⟨(FactorAssignmentProgram.moved b 151 854).regs,Function.update a.stacks 854 (Product.bytes out)⟩ := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases h1 : i=149 <;> by_cases h2 : i=150 <;> by_cases h3 : i=151 <;>
        by_cases h4 : i=854 <;>
        simp [b, state, h1, h2, h3, h4, h149, h150, h151, h854]
  rw [hout] at h3
  have honeBound := TruncatedRingProgram.empty_bytes_length_le (a:=one) ⟨hg.valid, hg.nodup⟩
  have houtBound := TruncatedRingProgram.empty_bytes_length_le (a:=out) ⟨ho.valid, ho.nodup⟩
  refine ⟨out,ho,hr,(7*(a.stacks 175).length+5)+((7*(a1.stacks 69).length+5)+
    (nl+(9*(b.stacks 151).length+8))),?_,_,h1.seq (h2.seq (he.seq h3))⟩
  dsimp [productBudget,byteBound]
  simp only [h175] at *
  have h69' : a1.stacks 69=Product.bytes one := by
    simpa [a1,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks] using h69
  simp only [h69']
  have hb151 : b.stacks 151=Product.bytes out := by simp [b,state]
  rw [hb151]
  omega

/-- The specialized record fold multiplies in the coefficient ring before any
additive shared-variable readout. Its empty list contributes the stored identity. -/
theorem foldRel_mul {n B d : ℕ} {R : Type*} [Monoid R]
    (decode : Raw n B d → R) (value : ℕ → R)
    (step : Raw n B d → ℕ → Raw n B d → Prop)
    (hstep : ∀ a id b, step a id b → decode b = decode a * value id)
    {ids : List ℕ} {seed out : Raw n B d}
    (hr : MomentsAssembly.Relational.FoldRel step ids seed out) :
    decode out = decode seed * (ids.map value).prod := by
  induction hr with
  | nil => simp
  | @cons id ids a b c hab hbc ih =>
    rw [ih, hstep a id b hab]
    simp only [List.map_cons, List.prod_cons, mul_assoc]

/-- This identity includes unused-factor groups and the empty product. -/
theorem foldRel_product {n B d : ℕ} {R : Type*} [Monoid R]
    (decode : Raw n B d → R) (value : ℕ → R)
    (step : Raw n B d → ℕ → Raw n B d → Prop)
    (hstep : ∀ a id b, step a id b → decode b = decode a * value id)
    {ids : List ℕ} {one out : Raw n B d}
    (hr : MomentsAssembly.Relational.FoldRel step ids one out)
    (hone : decode one = 1) : decode out = (ids.map value).prod := by
  rw [foldRel_mul decode value step hstep hr, hone, one_mul]

def uniformProductBudget (n B d u J T C : ℕ) : ℕ :=
  7 * T + 16 * byteBound n B d u J + (C + 17) * (T + 1) + 18

theorem productBudget_le (n B d u J T C : ℕ) (ids : List ℕ)
    (h : (ProgramEncoding.encodeRecords (records ids)).length ≤ T) :
    productBudget n B d u J C ids ≤ uniformProductBudget n B d u J T C := by
  have hl := loopBudget_le C ids
  have hm := Nat.mul_le_mul_left (C + 17) (Nat.add_le_add_right h 1)
  have hs := Nat.mul_le_mul_left 7 h
  dsimp [productBudget, uniformProductBudget]
  omega

/-- A fixed fourth power suffices for the full stored-ID loop controller once
its concrete per-factor budget C and structural input length T are supplied. -/
theorem uniformProductBudget_polynomial (n B d u J T C : ℕ) :
    uniformProductBudget n B d u J T C ≤
      256 * (n + B + d + u + J + T + C + 1) ^ 4 := by
  let a := n + B + d + u + J + T + C + 1
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hn : n ≤ a := by dsimp [a]; omega
  have hB : B ≤ a := by dsimp [a]; omega
  have hd : d ≤ a := by dsimp [a]; omega
  have hu : u ≤ a := by dsimp [a]; omega
  have hJ : J ≤ a := by dsimp [a]; omega
  have hT : T ≤ a := by dsimp [a]; omega
  have hC : C ≤ a := by dsimp [a]; omega
  have hm : uniformProductBudget n B d u J T C ≤
      uniformProductBudget a a a a a a a := by
    dsimp only [uniformProductBudget, byteBound]
    gcongr
  have he : uniformProductBudget a a a a a a a =
      32 * a ^ 4 + 96 * a ^ 3 + 33 * a ^ 2 + 25 * a + 35 := by
    unfold uniformProductBudget byteBound
    ring
  have h3 : a ^ 3 ≤ a ^ 4 := Nat.pow_le_pow_right ha (by decide)
  have h2 : a ^ 2 ≤ a ^ 4 := Nat.pow_le_pow_right ha (by decide)
  have h1 : a ≤ a ^ 4 := by simpa using Nat.pow_le_pow_right ha (show 1 ≤ 4 by decide)
  have h0 : 1 ≤ a ^ 4 := Nat.one_le_pow 4 a ha
  rw [he] at hm
  change uniformProductBudget n B d u J T C ≤ 256 * a ^ 4
  omega

/-- This prefix bound is local polynomial growth from a fixed structural
input bound. It is not a replacement for framing arbitrary retained callers. -/
theorem product_prefix_space {n B d u J T C k : ℕ} {ids : List ℕ}
    (a b : FactorAssignmentProgram.Data)
    (he : Eval FactorAssignmentProgram.product k a b)
    (hk : k ≤ productBudget n B d u J C ids)
    (hlen : (ProgramEncoding.encodeRecords (records ids)).length ≤ T) :
    Trace (compiled FactorAssignmentProgram.product 175 854) (k + 1)
      (a.withPC (some (compiled FactorAssignmentProgram.product 175 854).entry))
      (b.withPC none) ∧
    ∀ j z, j ≤ k + 1 →
      Trace (compiled FactorAssignmentProgram.product 175 854) j
        (a.withPC (some (compiled FactorAssignmentProgram.product 175 854).entry)) z →
      dataBits z ≤ stackBits a.stacks + uniformProductBudget n B d u J T C + 1 := by
  refine ⟨compiled_halt_trace he 175 854, ?_⟩
  intro j z hj hz
  have hb := trace_dataBits (compiled FactorAssignmentProgram.product 175 854) hz
  change dataBits z ≤ stackBits a.stacks + j at hb
  have ht := hk.trans (productBudget_le n B d u J T C ids hlen)
  omega

/-- The fixed structural boundary P is restored between assignments by the
semantic dictionary and frame invariants. This bound counts all896 caller stacks
and each prefix of this actual polynomial-time invocation. -/
theorem product_uniform_prefix_space {n B d u J T C k P : ℕ} {ids : List ℕ}
    (a b : FactorAssignmentProgram.Data)
    (he : Eval FactorAssignmentProgram.product k a b)
    (hk : k ≤ productBudget n B d u J C ids)
    (hlen : (ProgramEncoding.encodeRecords (records ids)).length ≤ T)
    (ha : ∀ i, (a.stacks i).length ≤ P) :
    ∀ j z, j ≤ k + 1 →
      Trace (compiled FactorAssignmentProgram.product 175 854) j
        (a.withPC (some (compiled FactorAssignmentProgram.product 175 854).entry)) z →
      dataBits z ≤ 896 * P + uniformProductBudget n B d u J T C + 1 := by
  intro j z hj hz
  have hb := (product_prefix_space a b he hk hlen).2 j z hj hz
  have hi := StreamResources.dataBits_le_mul
    (a.withPC (some (compiled FactorAssignmentProgram.product 175 854).entry)) ha
  change stackBits a.stacks ≤ 896 * P at hi
  omega

/-- Good-empty-support restores the same structural boundary after the whole
factor product. The proof uses the exact output-tape update from product_eval,
so retained caller words never inherit the transient prefix bound. -/
theorem product_return_bound {n B d u J P : ℕ}
    (a b : FactorAssignmentProgram.Data) (out : Raw n B d)
    (hframe : b.stacks = Function.update a.stacks 854 (Product.bytes out))
    (ha : ∀ i, (a.stacks i).length ≤ P)
    (hout : NativeSemantics.Good ∅ u J out)
    (hcapacity : byteBound n B d u J ≤ P) :
    ∀ i, (b.stacks i).length ≤ P := by
  have hbytes : (Product.bytes out).length ≤ byteBound n B d u J :=
    TruncatedRingProgram.empty_bytes_length_le (a := out) ⟨hout.valid, hout.nodup⟩
  intro i
  rw [hframe]
  by_cases hi : i = 854
  · subst i
    simpa only [Function.update_self] using hbytes.trans hcapacity
  · simpa only [Function.update_of_ne hi] using ha i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop
