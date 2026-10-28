import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceBankFrameCalls

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

def EmitterClean (a : Data) : Prop :=
  ∀ j : Fin 320, 256 ≤ j.val → j.val < 288 → j≠274 → a.stacks j=[]

theorem emitterClean_destinations (a : Data) (h : EmitterClean a) :
    ∀ j∈emitterDestinations,a.stacks j=[] := by
  intro j hj
  simp only [emitterDestinations,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    exact h _ (by decide) (by decide) (by decide)

theorem stageEmitter_ready (a : Data) (hclean : EmitterClean a)
    (tables : UniversalRowLoop.Tables) (width rowWidth : List Bool) (positions : List ℕ)
    (hv : a.stacks 67=tables.values.flatten) (hi : a.stacks 308=tables.inverses.flatten)
    (hn : a.stacks 309=tables.negatives.flatten) (hr : a.stacks 310=tables.rows.flatten)
    (hp : a.stacks 71=UniversalRowTermProgram.indices positions)
    (hw : a.stacks 311=width) (hrw : a.stacks 312=rowWidth) :
    UniversalRowLoop.ready tables width rowWidth positions
      (projectState emitterRegs emitterPorts (Staging.result 0 1 stageEmitterOps a)) := by
  have hs := stageEmitter_stacks a (emitterClean_destinations a hclean)
  have hfield (j : Fin 32) :
      (projectState emitterRegs emitterPorts (Staging.result 0 1 stageEmitterOps a)).stacks j=
        emitterStacks a (emitterPorts j) := congrFun hs _
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hfield]; simpa [emitterStacks,emitterPorts] using hv
  · rw [hfield]; simpa [emitterStacks,emitterPorts] using hi
  · rw [hfield]; simpa [emitterStacks,emitterPorts] using hn
  · rw [hfield]; simpa [emitterStacks,emitterPorts] using hr
  · rw [hfield]; simpa [emitterStacks,emitterPorts] using hp
  · rw [hfield]; simpa [emitterStacks,emitterPorts] using hw
  · rw [hfield]; simpa [emitterStacks,emitterPorts] using hrw
  · rw [hfield]
    simp [emitterStacks,emitterPorts,UniversalRowFactorLoop.indexWord,
      hclean 272 (by decide) (by decide) (by decide)]
  · intro j hj
    rw [hfield]
    fin_cases j <;> simp_all [emitterStacks,emitterPorts,EmitterClean]

def clearedStacks (a : Data) : Fin 320 → List Bool :=
  fun j=>if j∈cleanupPorts then [] else a.stacks j

theorem prepend_cleanup {first second : Code} {n m : ℕ} {a b c : Data}
    (hf : Eval first n a b) (hs : Eval (.seq second cleanup) m b c) :
    Eval (.seq (.seq first second) cleanup) (n+m) a c := by
  cases hs with
  | seq hg hc => simpa [Nat.add_assoc] using (hf.seq hg).seq hc

theorem cleanup_emitter_stacks (a b : Data) (word : List Bool)
    (hb : b.stacks=Function.update (Function.update (emitterStacks a) 274 []) 287 word) :
    (Staging.result 0 1 cleanupOps b).stacks=Function.update (clearedStacks a) 287 word := by
  funext j
  rw [cleanup_stacks,hb]
  by_cases hj : j=287
  · subst j; simp [cleanupPorts]
  · by_cases hc : j∈cleanupPorts
    · simp [hc,hj,clearedStacks]
    · have hn (i : Fin 320) (hi : i∈cleanupPorts) : j≠i := by
        intro h; subst j; exact hc hi
      simp [hc,hj,clearedStacks,emitterStacks,
        hn 274 (by decide),hn 280 (by decide),hn 281 (by decide),hn 282 (by decide),
        hn 283 (by decide),hn 284 (by decide),hn 285 (by decide),hn 286 (by decide),
        hn 259 (by decide),hn 266 (by decide),hn 269 (by decide)]

theorem emitterStacks_length_le (a : Data) (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B)
    (j : Fin 320) : (emitterStacks a j).length ≤ B := by
  have upd (f : Fin 320 → List Bool) (hf : ∀ i,(f i).length ≤ B)
      (k : Fin 320) (v : List Bool) (hv : v.length ≤ B) :
      ∀ i,(Function.update f k v i).length ≤ B := by
    intro i
    by_cases hi : i=k
    · subst i; simpa using hv
    · simpa [hi] using hf i
  have h280 := upd _ hB 280 _ (hB 67)
  have h281 := upd _ h280 281 _ (hB 308)
  have h282 := upd _ h281 282 _ (hB 309)
  have h283 := upd _ h282 283 _ (hB 310)
  have h284 := upd _ h283 284 _ (hB 71)
  have h285 := upd _ h284 285 _ (hB 311)
  have h286 := upd _ h285 286 _ (hB 312)
  have h259 := upd _ h286 259 _ (hB 313)
  have h266 := upd _ h259 266 _ (hB 314)
  exact upd _ h266 269 _ (hB 47) j

theorem cleanup_emitter_cost (a b : Data) (word : List Bool) (B : ℕ)
    (hB : ∀ j,(a.stacks j).length ≤ B)
    (hb : b.stacks=Function.update (Function.update (emitterStacks a) 274 []) 287 word) :
    Staging.cost 0 1 cleanupOps b ≤ 120*B+180 := by
  apply cleanup_cost_le
  intro j hj
  have hn : j≠287 := by intro h; subst j; exact (by decide : (287:Fin 320)∉cleanupPorts) hj
  rw [hb]
  rw [Function.update_of_ne hn]
  by_cases he : j=274
  · subst j; simp
  · simpa [Function.update_of_ne he] using emitterStacks_length_le a B hB j

/-- The prepared emitter is called physically and its workspace is cleared.
The scalar cache words remain input data, not an input polynomial oracle. -/
theorem stage_emit_cleanup_eval (a : Data) (ht : a.stacks 319=[]) (hclean : EmitterClean a)
    (tables : UniversalRowLoop.Tables) (width rowWidth : List Bool) (positions : List ℕ)
    (valid : UniversalRowLoop.Valid tables width rowWidth positions)
    (hv : a.stacks 67=tables.values.flatten) (hi : a.stacks 308=tables.inverses.flatten)
    (hn : a.stacks 309=tables.negatives.flatten) (hr : a.stacks 310=tables.rows.flatten)
    (hp : a.stacks 71=UniversalRowTermProgram.indices positions)
    (hw : a.stacks 311=width) (hrw : a.stacks 312=rowWidth)
    (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B) :
    let word := UniversalRowProgram.rowCode (a.stacks 313) (a.stacks 314)
      (a.stacks 313++a.stacks 314)
      (UniversalRowDataProgram.row tables positions (a.stacks 274) (a.stacks 47))
    ∃ n ≤ 7*emitterSize a+50+
      UniversalRowSourceProgram.bound tables width rowWidth positions
        (a.stacks 274) (a.stacks 47) (a.stacks 313) (a.stacks 314)+120*B+180,
      ∃ b : Data, Eval (.seq (.seq stageEmitter emit) cleanup) n a b ∧
        b.stacks=Function.update (clearedStacks a) 287 word := by
  intro word
  let p := Staging.result 0 1 stageEmitterOps a
  have hs : p.stacks=emitterStacks a := stageEmitter_stacks a (emitterClean_destinations a hclean)
  have hready := stageEmitter_ready a hclean tables width rowWidth positions hv hi hn hr hp hw hrw
  obtain ⟨ne,hne,b,he,hbs⟩ := emit_eval tables width rowWidth positions valid
    (a.stacks 274) (a.stacks 47) (a.stacks 313) (a.stacks 314) p hready
    (by simp [hs,emitterStacks]) (by simp [hs,emitterStacks])
    (by simp [hs,emitterStacks]) (by simp [hs,emitterStacks])
    (by simpa [hs,emitterStacks] using hclean 270 (by decide) (by decide) (by decide))
    (by simpa [hs,emitterStacks] using hclean 273 (by decide) (by decide) (by decide))
    (by simpa [hs,emitterStacks] using hclean 287 (by decide) (by decide) (by decide))
  have hb : b.stacks=Function.update (Function.update (emitterStacks a) 274 []) 287 word := by
    simpa only [hs,word] using hbs
  have hbt : b.stacks 319=[] := by
    simp [hb,emitterStacks,ht]
  have hc := cleanup_emitter_cost a b word B hB hb
  refine ⟨Staging.cost 0 1 stageEmitterOps a+(ne+Staging.cost 0 1 cleanupOps b),?_,
    Staging.result 0 1 cleanupOps b,
    by simpa [Nat.add_assoc] using ((stageEmitter_eval a ht).seq he).seq (cleanup_eval b hbt),
    cleanup_emitter_stacks a b word hb⟩
  rw [stageEmitter_cost]
  omega

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
