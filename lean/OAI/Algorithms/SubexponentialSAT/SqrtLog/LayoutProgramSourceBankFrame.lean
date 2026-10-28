import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceBankFrameFinish

namespace OAI.Algorithms

/-! Composition for the actual SourceBank. Premises about table and mismatch
execution are traces of their fixed native programs, not free callbacks. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def vectorState (a : Data) (rf : Fin 16 → Bool) (bits : List Bool) : Data :=
  ⟨rf,Function.update (Staging.result 0 1 stageTypesOps a).stacks 67 bits⟩

def branchState (a : Data) (rf : Fin 16 → Bool) (bits indices : List Bool) : Data :=
  ⟨rf,Function.update (Function.update (Staging.result 0 1 stageTypesOps a).stacks 67 bits) 71 indices⟩

theorem branch_cleared (a : Data) (rf : Fin 16 → Bool) (bits indices : List Bool)
    (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[]) :
    clearedStacks (branchState a rf bits indices)=clearedStacks a := by
  apply clearedStacks_eq
  intro j hj
  have hn (i : Fin 320) (hi : i∈cleanupPorts) : j≠i := by
    intro he; subst j; exact hj hi
  simp [branchState,stageTypes_stacks a h23 h24,
    hn 23 (by decide),hn 24 (by decide),hn 67 (by decide),hn 71 (by decide)]

theorem branch_sourceWord (a : Data) (rf : Fin 16 → Bool) (bits indices : List Bool)
    (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[])
    (tables : UniversalRowLoop.Tables) (positions : List ℕ) :
    sourceWord tables positions (branchState a rf bits indices)=
      UniversalRowProgram.rowCode (a.stacks 313) (a.stacks 314) (a.stacks 313++a.stacks 314)
        (UniversalRowDataProgram.row tables positions
          (if a.stacks 289=a.stacks 292 then a.stacks 314 else a.stacks 313) (a.stacks 47)) := by
  simp [sourceWord,deltaWord,branchState,stageTypes_stacks a h23 h24]

/-- Fully measured prepare/native-table/native-mismatch/compare/emitter/cleanup
composition, with an exact frame on every caller stack. -/
theorem universal_cleanup_eval (a : Data) (ht : a.stacks 319=[])
    (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[])
    (bits indices : List Bool) (rv rm : Fin 16 → Bool) (nv nm : ℕ)
    (hvector : Trace LayoutSourceValuesProgram.Native.tableProgram nv
      ((projectState id vectorPorts (Staging.result 0 1 stageTypesOps a)).withPC
        (some LayoutSourceValuesProgram.Native.tableProgram.entry))
      ((⟨rv,Function.update (projectState id vectorPorts
        (Staging.result 0 1 stageTypesOps a)).stacks 67 bits⟩ : State 16 256).withPC none))
    (hmismatch : Eval mismatches nm (vectorState a rv bits) (branchState a rm bits indices))
    (tables : UniversalRowLoop.Tables) (width rowWidth : List Bool) (positions : List ℕ)
    (valid : UniversalRowLoop.Valid tables width rowWidth positions)
    (hclean : EmitterClean (branchState a rm bits indices))
    (h274 : (branchState a rm bits indices).stacks 274=[])
    (h0 : (branchState a rm bits indices).stacks 0=[])
    (h1 : (branchState a rm bits indices).stacks 1=[])
    (h2 : (branchState a rm bits indices).stacks 2=[])
    (h3 : (branchState a rm bits indices).stacks 3=[])
    (hv : bits=tables.values.flatten)
    (hi : a.stacks 308=tables.inverses.flatten) (hn : a.stacks 309=tables.negatives.flatten)
    (hr : a.stacks 310=tables.rows.flatten)
    (hp : indices=UniversalRowTermProgram.indices positions)
    (hw : a.stacks 311=width) (hrw : a.stacks 312=rowWidth)
    (B : ℕ) (hB : ∀ j,((branchState a rm bits indices).stacks j).length ≤ B) :
    ∃ n ≤ Staging.cost 0 1 stageTypesOps a+nv+nm+
        finishBound tables width rowWidth positions (branchState a rm bits indices) B,
      ∃ b : Data, Eval (.seq universal cleanup) n a b ∧
        b.stacks=Function.update (clearedStacks a) 287
          (sourceWord tables positions (branchState a rm bits indices)) := by
  let p := Staging.result 0 1 stageTypesOps a
  obtain ⟨q,hq,hqs,hqr⟩ := vector_lifted p bits rv hvector
  have hqeq : q=vectorState a rv bits := SubexpScanPrimitives.state_ext hqr hqs
  rw [hqeq] at hq
  let z := branchState a rm bits indices
  have hz319 : z.stacks 319=[] := by
    simp [z,branchState,stageTypes_stacks a h23 h24,ht]
  obtain ⟨nf,hnf,b,hf,hbs⟩ := finish_universal_eval z hz319 hclean h274 h0 h1 h2 h3
    tables width rowWidth positions valid
    (by simpa [z,branchState] using hv)
    (by simpa [z,branchState,stageTypes_stacks a h23 h24] using hi)
    (by simpa [z,branchState,stageTypes_stacks a h23 h24] using hn)
    (by simpa [z,branchState,stageTypes_stacks a h23 h24] using hr)
    (by simpa [z,branchState] using hp)
    (by simpa [z,branchState,stageTypes_stacks a h23 h24] using hw)
    (by simpa [z,branchState,stageTypes_stacks a h23 h24] using hrw) B hB
  have he := prepend_cleanup (stageTypes_eval a ht)
    (prepend_cleanup hq (prepend_cleanup hmismatch hf))
  dsimp only [z] at hnf
  refine ⟨Staging.cost 0 1 stageTypesOps a+(nv+(nm+nf)),by omega,b,he,?_⟩
  simpa only [z,branch_cleared a rm bits indices h23 h24] using hbs

theorem literal_cleanup_eval (src : Fin 320) (hsrc : src=313 ∨ src=314) (a : Data)
    (ht : a.stacks 319=[]) (h315 : a.stacks 315=[]) (h316 : a.stacks 316=[])
    (h287 : a.stacks 287=[]) (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B) :
    ∃ n ≤ 14*(a.stacks src).length+19+120*B+180,
      ∃ b : Data, Eval (.seq (literal src) cleanup) n a b ∧
        b.stacks=Function.update (clearedStacks a) 287
          (SubexponentialSAT.SubexpKernelControl.pushWord (a.stacks src)) := by
  obtain ⟨b,hb,hbs⟩ := literal_eval src hsrc a h315 h316 h287
  have hbt : b.stacks 319=[] := by simp [hbs,ht]
  have hc : Staging.cost 0 1 cleanupOps b ≤ 120*B+180 := by
    apply cleanup_cost_le
    intro j hj
    have hne : j≠287 := by intro h; subst j; exact (by decide : (287:Fin 320)∉cleanupPorts) hj
    simpa [hbs,hne] using hB j
  refine ⟨14*(a.stacks src).length+19+Staging.cost 0 1 cleanupOps b,by omega,
    Staging.result 0 1 cleanupOps b,hb.seq (cleanup_eval b hbt),?_⟩
  funext j
  rw [cleanup_stacks,hbs]
  by_cases hj : j=287
  · subst j; simp [cleanupPorts]
  · simp [clearedStacks,hj]

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
