import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.SupportSelectionPrimitives

namespace OAI.Algorithms

/-! One physical vertex visit: lookup, head selection, and support emission. -/

namespace SubexponentialSAT.Subexp.SupportSelectionProgram

open BitProgram StructuredCalls SubexpScanPrimitives ConstructivePacking


private theorem unary_eq_iff (m n : ℕ) : unary m = unary n ↔ m = n := by
  constructor
  · intro h
    simpa using congrArg List.length h
  · rintro rfl
    rfl

def covered : Code := .seq GlobalBasisRowPrepare.headColor
  (.seq (copy 35 7) (.seq compareColors selectColor))

def core : Code := .seq (copy 39 34)
  (.seq GlobalBasisRowPrepare.metadata (.ite 6 covered (emit 1 (by decide))))

def visit : Code := .seq core cleanup

private theorem covered_eval {r Q Δ : ℕ} (u : MulticolorTypes.UniversalType r Q Δ)
    (t : Fin Q) (g v : ℕ) (d : Data)
    (hu : d.stacks 36 = CollisionProgram.encodeType u)
    (ht : d.stacks 32 = unary t.val) (hr : d.stacks 38 = unary r)
    (hg : d.stacks 35 = unary g) (hv : d.stacks 34 = unary v)
    (hz : ∀ j ∈ ([4,7,16,17,18,19,20,21,42] : List (Fin 64)), d.stacks j = []) :
    ∃ n e, n ≤ SubexpHeadColorProgram.budget t.val r + 7*g + 9*r + 5*v + 20 ∧
      Eval covered n d e ∧
      e.stacks 0 = (if (u.head t).val = g then record v ++ d.stacks 0 else d.stacks 0) ∧
      e.stacks 1 = d.stacks 1 ∧
      (∀ j, j ≠ 0 → j ≠ 4 → j ≠ 7 → j ≠ 34 → e.stacks j = d.stacks j) := by
  have hc : SubexpHeadColorProgram.Clean
      (projectState GlobalBasisRowPrepare.smallRegs GlobalBasisRowPrepare.headPorts d) := by
    intro i hi
    apply hz (GlobalBasisRowPrepare.headPorts i)
    fin_cases i <;> first
    | exact absurd hi (by decide)
    | decide
  obtain ⟨nh, a, hnh, hh, hsa, _⟩ :=
    GlobalBasisRowPrepare.headColor_eval u t d hu ht hr hc
  let b := afterCopy a 35 7 0 1
  have hcopy : Eval (copy 35 7) (7*g+5) a b := by
    have he := copy_eval a 35 7 42 0 1 (by decide) (by decide) (by decide) (by decide)
      (by simp [hsa, hz])
    simpa only [copy, b, hsa, Function.update_of_ne (by decide : (35 : Fin 64) ≠ 4),
      hg, List.length_replicate] using he
  have hb4 : b.stacks 4 = unary (u.head t).val := by simp [b, afterCopy, StackRoutines.copyStacks, hsa]
  have hb7 : b.stacks 7 = unary g := by simp [b, afterCopy, StackRoutines.copyStacks, hsa, hz, hg]
  have hb34 : b.stacks 34 = unary v := by simp [b, afterCopy, StackRoutines.copyStacks, hsa, hv]
  obtain ⟨nc, c, left, right, hnc, hec, hsc, hflag, _, _⟩ := compareColors_eval b
  have hflag' : c.regs 4 = decide ((u.head t).val = g) := by
    simpa only [hb4, hb7, unary_eq_iff] using hflag
  have hc34 : c.stacks 34 = unary v := by simp [hsc, hb34]
  obtain ⟨ns, e, hns, hes, hse⟩ := selectColor_eval c v hc34
  refine ⟨nh + (7*g+5 + (nc+ns)), e, ?_, hh.seq (hcopy.seq (hec.seq hes)), ?_, ?_, ?_⟩
  · have hlt := (u.head t).isLt
    simp only [hb4, List.length_replicate] at hnc
    omega
  · simp [hse, hflag', hsc, b, afterCopy, StackRoutines.copyStacks, hsa]
  · simp [hse, hsc, b, afterCopy, StackRoutines.copyStacks, hsa]
  · intro j h0 h4 h7 h34
    simp [hse, hsc, b, afterCopy, StackRoutines.copyStacks, hsa, h0, h4, h7, h34]

variable {D r Q Δ : ℕ}

/-- The complete prefix consists solely of actual fixed subroutine calls. -/
theorem core_eval (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (g : ℕ) (v : Fin D) (d : Data)
    (h33 : d.stacks 33 = SelectorProgram.rawRecords
      (PackingMetadata.records P (fun w => unary w.val) CollisionProgram.encodeType))
    (h32 : d.stacks 32 = unary t.val) (h38 : d.stacks 38 = unary r)
    (h35 : d.stacks 35 = unary g) (h39 : d.stacks 39 = unary v.val)
    (hc : Clean d) :
    ∃ n e, n ≤ prefixBound (d.stacks 33).length v.val t.val r g ∧
      Eval core n d e ∧
      e.stacks 0 = (if colorAt P t g v then record v.val ++ d.stacks 0 else d.stacks 0) ∧
      e.stacks 1 = (if outsideAt P v then record v.val ++ d.stacks 1 else d.stacks 1) ∧
      CoreFrame d e := by
  let records := PackingMetadata.records P (fun w => unary w.val) CollisionProgram.encodeType
  let m := PackingMetadata.value P CollisionProgram.encodeType v
  have hfind : records.lookup (unary v.val) = some m.encode :=
    PackingMetadata.lookup_eq P (fun w => unary w.val) CollisionProgram.encodeType
      (fun a b h => Fin.ext ((unary_eq_iff a.val b.val).mp h)) v
  let a := afterCopy d 39 34 0 1
  have hzero := hc
  dsimp only [Clean] at hzero
  have hcopy : Eval (copy 39 34) (7*v.val+5) d a := by
    have he := copy_eval d 39 34 42 0 1 (by decide) (by decide) (by decide) (by decide)
      (hzero 42 (by decide))
    simpa only [copy, a, h39, List.length_replicate] using he
  have ha : projectState GlobalBasisRowPrepare.metadataRegs GlobalBasisRowPrepare.metadataPorts a =
      GlobalBasisMetadata.inputState (a.regs ∘ GlobalBasisRowPrepare.metadataRegs)
        (SelectorProgram.rawRecords records) (unary v.val) := by
    apply state_ext
    · rfl
    · funext i
      fin_cases i <;> simp [projectState, GlobalBasisRowPrepare.metadataPorts,
        GlobalBasisMetadata.inputState, GlobalBasisMetadata.work, a, afterCopy,
        StackRoutines.copyStacks, h33, h39, hzero, records]
  obtain ⟨nm, b, hnm, hm, hsb, hflag⟩ :=
    GlobalBasisRowPrepare.metadata_eval records (unary v.val) m a hfind ha
  have hnm' : nm ≤ 400 * ((d.stacks 33).length + v.val + 1)^2 := by
    simpa only [GlobalBasisMetadata.volume, List.length_replicate, records, ← h33] using hnm
  cases hlookup : P.lookup v with
  | none =>
    have heqm : m = .leftover (PackingMetadata.unary (P.leftovers.idxOf v)) := by
      simp [m, PackingMetadata.value, hlookup]
    simp only [heqm, GlobalBasisMetadata.Metadata.block, GlobalBasisMetadata.Metadata.typeCode,
      GlobalBasisMetadata.Metadata.rank, GlobalBasisMetadata.Metadata.coveredFlag] at hsb hflag
    have hb34 : b.stacks 34 = unary v.val := by
      simp [hsb, a, afterCopy, StackRoutines.copyStacks, h39, hzero]
    obtain ⟨e, he, hse⟩ := emit_eval 1 (by decide) b v.val hb34
    refine ⟨7*v.val+5 + (nm + (5*v.val+7+1)), e, ?_,
      hcopy.seq (hm.seq (Eval.ite_false hflag he)), ?_, ?_, ?_⟩
    · unfold prefixBound
      omega
    · simp [colorAt, hlookup, hse, hsb, a, afterCopy, StackRoutines.copyStacks]
    · simp [outsideAt, hlookup, hse, hsb, a, afterCopy, StackRoutines.copyStacks]
    · intro j h0 h1 hj
      have h3 : j ≠ 3 := by intro h; subst j; exact hj (by decide)
      have h4 : j ≠ 4 := by intro h; subst j; exact hj (by decide)
      have h5 : j ≠ 5 := by intro h; subst j; exact hj (by decide)
      have h7 : j ≠ 7 := by intro h; subst j; exact hj (by decide)
      have h34 : j ≠ 34 := by intro h; subst j; exact hj (by decide)
      have h36 : j ≠ 36 := by intro h; subst j; exact hj (by decide)
      simp [hse, hsb, a, afterCopy, StackRoutines.copyStacks, h1, h3, h5, h34, h36]
  | some z =>
    rcases z with ⟨block, u⟩
    have heqm : m = .covered (PackingMetadata.unary block.val) (CollisionProgram.encodeType u) := by
      simp [m, PackingMetadata.value, hlookup]
    simp only [heqm, GlobalBasisMetadata.Metadata.block, GlobalBasisMetadata.Metadata.typeCode,
      GlobalBasisMetadata.Metadata.rank, GlobalBasisMetadata.Metadata.coveredFlag] at hsb hflag
    have hu : b.stacks 36 = CollisionProgram.encodeType u := by simp [hsb]
    have ht : b.stacks 32 = unary t.val := by simp [hsb, a, afterCopy, StackRoutines.copyStacks, h32]
    have hr : b.stacks 38 = unary r := by simp [hsb, a, afterCopy, StackRoutines.copyStacks, h38]
    have hg : b.stacks 35 = unary g := by simp [hsb, a, afterCopy, StackRoutines.copyStacks, h35]
    have hv : b.stacks 34 = unary v.val := by
      simp [hsb, a, afterCopy, StackRoutines.copyStacks, h39, hzero]
    have hz : ∀ j ∈ ([4,7,16,17,18,19,20,21,42] : List (Fin 64)), b.stacks j = [] := by
      intro j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [hsb, a, afterCopy, StackRoutines.copyStacks, hzero]
    obtain ⟨nb, e, hnb, he, he0, he1, hef⟩ := covered_eval u t g v.val b hu ht hr hg hv hz
    refine ⟨7*v.val+5 + (nm + (nb+1)), e, ?_,
      hcopy.seq (hm.seq (Eval.ite_true hflag he)), ?_, ?_, ?_⟩
    · unfold prefixBound
      omega
    · simp [colorAt, hlookup, he0, hsb, a, afterCopy, StackRoutines.copyStacks]
    · simp [outsideAt, hlookup, he1, hsb, a, afterCopy, StackRoutines.copyStacks]
    · intro j h0 h1 hj
      have h3 : j ≠ 3 := by intro h; subst j; exact hj (by decide)
      have h4 : j ≠ 4 := by intro h; subst j; exact hj (by decide)
      have h5 : j ≠ 5 := by intro h; subst j; exact hj (by decide)
      have h7 : j ≠ 7 := by intro h; subst j; exact hj (by decide)
      have h34 : j ≠ 34 := by intro h; subst j; exact hj (by decide)
      have h36 : j ≠ 36 := by intro h; subst j; exact hj (by decide)
      rw [hef j h0 h4 h7 h34]
      simp [hsb, a, afterCopy, StackRoutines.copyStacks, h3, h5, h34, h36]

/-- Scratch cleanup is charged from the length growth in the actual prefix
trace. Only the two support accumulators change during a complete visit. -/
theorem visit_eval (P : PackingData (Fin D) (MulticolorTypes.UniversalType r Q Δ))
    (t : Fin Q) (g : ℕ) (v : Fin D) (d : Data)
    (h33 : d.stacks 33 = SelectorProgram.rawRecords
      (PackingMetadata.records P (fun w => unary w.val) CollisionProgram.encodeType))
    (h32 : d.stacks 32 = unary t.val) (h38 : d.stacks 38 = unary r)
    (h35 : d.stacks 35 = unary g) (h39 : d.stacks 39 = unary v.val)
    (hc : Clean d) :
    ∃ n e, n ≤ visitBound (d.stacks 33).length v.val t.val r g ∧
      Eval visit n d e ∧
      e.stacks = Function.update (Function.update d.stacks 0
        (if colorAt P t g v then record v.val ++ d.stacks 0 else d.stacks 0)) 1
        (if outsideAt P v then record v.val ++ d.stacks 1 else d.stacks 1) := by
  obtain ⟨n, e, hn, he, he0, he1, hf⟩ := core_eval P t g v d h33 h32 h38 h35 h39 hc
  have hlen : ∀ j ∈ cleanupPorts, (e.stacks j).length ≤ n + 1 := by
    intro j hj
    have h := SequentialProgram.trace_stack_length_le (compiled_halt_trace he 0 0) j
    simpa only [StructuredProgram.State.withPC, Clean.cleanup d hc j hj, List.length_nil,
      Nat.zero_add] using h
  obtain ⟨m, hm, f, hef, hfs⟩ := cleanup_eval e (n+1) hlen
  refine ⟨n+m, f, ?_, he.seq hef, ?_⟩
  · unfold visitBound
    norm_num [cleanupPorts] at hm
    omega
  · funext j
    rw [hfs j]
    by_cases hj0 : j = 0
    · subst j
      simp [cleanupPorts, he0]
    by_cases hj1 : j = 1
    · subst j
      simp [cleanupPorts, he1]
    by_cases hj : j ∈ cleanupPorts
    · simp [hj, hj0, hj1, Clean.cleanup d hc j hj]
    · simp [hj, hj0, hj1, hf j hj0 hj1 hj]

end SubexponentialSAT.Subexp.SupportSelectionProgram

end OAI.Algorithms
