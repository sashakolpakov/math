import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpGlobalRowSelection
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingMetadata
import OAI.Algorithms.SubexponentialSAT.SubexpIncidenceSlotBounds

namespace OAI.Algorithms

/-! Instantiation of the physical dispatcher at the computed packing lookup.
The table equality is an input-storage condition. The packing extractor must
establish it from its actual output; no polynomial-row equality is assumed. -/

namespace SubexponentialSAT.SubexpGlobalRowPacking

open BitProgram StructuredCalls SubexpDenseRowTableProgram
  SubexpGlobalRowBranch SubexpGlobalRowLookup SubexpGlobalRowSelection
  Subexp.ConstructivePacking

variable {D : ℕ} {U : Type*} [DecidableEq U]

def key (v : Fin D) : Word := unary v.val

theorem key_injective : Function.Injective (key (D := D)) := by
  intro v w h
  apply Fin.ext
  exact unary_eq_iff _ _ |>.mp h

def records (P : PackingData (Fin D) U) (encodeType : U → Word) : List (Word × Word) :=
  Subexp.PackingMetadata.records P key encodeType

def table (P : PackingData (Fin D) U) (encodeType : U → Word) : Word :=
  Subexp.SelectorProgram.rawRecords (records P encodeType)

def volume (P : PackingData (Fin D) U) (encodeType : U → Word) (v : Fin D) : ℕ :=
  Subexp.GlobalBasisMetadata.volume (records P encodeType) (key v)

theorem lookup_covered (P : PackingData (Fin D) U) (encodeType : U → Word)
    (v : Fin D) (i : Fin P.blockCount) (u : U) (hv : P.lookup v = some (i,u)) :
    (records P encodeType).lookup (unary v.val) =
      some (Subexp.GlobalBasisMetadata.Metadata.covered (unary i.val) (encodeType u)).encode := by
  have h := Subexp.PackingMetadata.lookup_eq P key encodeType key_injective v
  simpa [records, key, Subexp.PackingMetadata.value, hv,
    Subexp.PackingMetadata.unary, unary] using h

theorem lookup_leftover (P : PackingData (Fin D) U) (encodeType : U → Word)
    (v : Fin D) (hv : P.lookup v = none) :
    (records P encodeType).lookup (unary v.val) =
      some (Subexp.GlobalBasisMetadata.Metadata.leftover (unary (P.leftovers.idxOf v))).encode := by
  have h := Subexp.PackingMetadata.lookup_leftover P key encodeType key_injective v hv
  simpa [records, key, Subexp.PackingMetadata.unary, unary] using h

/-- The unselected branch generates the identity constant from the actual
cached zero/one word and returns with all metadata scratch restored. -/
theorem prepare_leftover (universal : Code) (P : PackingData (Fin D) U)
    (encodeType : U → Word) (v w : Fin D) (hv : P.lookup v = none) (a : Data)
    (htable : a.stacks 265 = table P encodeType)
    (hsource : a.stacks 260 = key v) (htarget : a.stacks 262 = key w)
    (ha : HighClean a) (h26 : a.stacks 26 = []) :
    ∃ n ≤ 400 * (volume P encodeType v)^2 + 18 * v.val + 9 * w.val +
      14 * (a.stacks (constantPort (decide (v.val = w.val)))).length +
      2 * (P.leftovers.idxOf v) + 99, ∃ regs,
      Eval (prepare universal) n a
        ⟨regs, Function.update a.stacks 26
          (literalWord (a.stacks (constantPort (decide (v.val = w.val)))))⟩ := by
  simpa only [volume, key, unary, List.length_replicate] using
    prepare_leftover_run universal a (records P encodeType) v.val w.val
      (unary (P.leftovers.idxOf v)) (lookup_leftover P encodeType v hv)
      htable hsource htarget ha h26

/-- Covered-to-leftover rows execute the zero branch. The lookup facts are
proved directly from the same packing used by the layout semantics. -/
theorem prepare_rightLeftover (universal : Code) (P : PackingData (Fin D) U)
    (encodeType : U → Word) (v w : Fin D) (i : Fin P.blockCount) (u : U)
    (hv : P.lookup v = some (i,u)) (hw : P.lookup w = none) (a : Data)
    (htable : a.stacks 265 = table P encodeType)
    (hsource : a.stacks 260 = key v) (htarget : a.stacks 262 = key w)
    (ha : HighClean a) (h26 : a.stacks 26 = []) :
    ∃ n ≤ 400 * (volume P encodeType v)^2 + 400 * (volume P encodeType w)^2 +
      14 * (a.stacks 131).length +
      2 * (i.val + (encodeType u).length + P.leftovers.idxOf w) + 75,
      ∃ regs, Eval (prepare universal) n a
        ⟨regs, Function.update a.stacks 26 (literalWord (a.stacks 131))⟩ := by
  obtain ⟨n, hn, b, he, h5, h6, hb⟩ := rightLeftover_run a (records P encodeType) v.val w.val
    (unary i.val) (encodeType u) (unary (P.leftovers.idxOf w))
    (lookup_covered P encodeType v i u hv) (lookup_leftover P encodeType w hw)
    htable hsource htarget ha
  obtain ⟨regs, hprepare⟩ := prepare_zero_after_run universal a b
    (.covered (unary i.val) (encodeType u)) (.leftover (unary (P.leftovers.idxOf w)))
    ha h26 he h5 h6 hb
  refine ⟨_, ?_, regs, hprepare⟩
  change n ≤ 400 * (volume P encodeType v)^2 + 400 * (volume P encodeType w)^2 + 4 at hn
  simp only [Subexp.GlobalBasisMetadata.Metadata.block,
    Subexp.GlobalBasisMetadata.Metadata.typeCode, Subexp.GlobalBasisMetadata.Metadata.rank,
    List.length_nil, unary, List.length_replicate]
  omega

/-- Different covered blocks generate zero after an actual block-word
comparison; no branch is selected from a supplied Boolean. -/
theorem prepare_differentBlock (universal : Code) (P : PackingData (Fin D) U)
    (encodeType : U → Word) (v w : Fin D) (i j : Fin P.blockCount) (u y : U)
    (hij : i ≠ j) (hv : P.lookup v = some (i,u)) (hw : P.lookup w = some (j,y)) (a : Data)
    (htable : a.stacks 265 = table P encodeType)
    (hsource : a.stacks 260 = key v) (htarget : a.stacks 262 = key w)
    (ha : HighClean a) (h26 : a.stacks 26 = []) :
    ∃ n ≤ 400 * (volume P encodeType v)^2 + 400 * (volume P encodeType w)^2 +
      18 * i.val + 9 * j.val + 14 * (a.stacks 131).length +
      2 * (i.val + (encodeType u).length + j.val + (encodeType y).length) + 101,
      ∃ regs, Eval (prepare universal) n a
        ⟨regs, Function.update a.stacks 26 (literalWord (a.stacks 131))⟩ := by
  have hne : unary i.val ≠ unary j.val := by
    intro h
    exact hij (Fin.ext ((unary_eq_iff _ _).mp h))
  obtain ⟨n, hn, b, he, h5, h6, hb⟩ := differentBlock_run a (records P encodeType) v.val w.val
    (unary i.val) (encodeType u) (unary j.val) (encodeType y) hne
    (lookup_covered P encodeType v i u hv) (lookup_covered P encodeType w j y hw)
    htable hsource htarget ha
  obtain ⟨regs, hprepare⟩ := prepare_zero_after_run universal a b
    (.covered (unary i.val) (encodeType u)) (.covered (unary j.val) (encodeType y))
    ha h26 he h5 h6 hb
  refine ⟨_, ?_, regs, hprepare⟩
  change n ≤ 400 * (volume P encodeType v)^2 + 400 * (volume P encodeType w)^2 +
    18 * (unary i.val).length + 9 * (unary j.val).length + 30 at hn
  simp only [unary, List.length_replicate] at hn
  simp only [Subexp.GlobalBasisMetadata.Metadata.block,
    Subexp.GlobalBasisMetadata.Metadata.typeCode, Subexp.GlobalBasisMetadata.Metadata.rank,
    List.length_nil, unary, List.length_replicate]
  omega

/-- Same-block classification leaves the exact two type encodings and the
one-based physical prefix slot for the universal row producer. -/
theorem classify_sameBlock (P : PackingData (Fin D) U) (encodeType : U → Word)
    (v w : Fin D) (i : Fin P.blockCount) (u y : U)
    (hv : P.lookup v = some (i,u)) (hw : P.lookup w = some (i,y))
    (scopes : List (List ℕ)) (e : ℕ) (he : e ≤ scopes.length) (a : Data)
    (htable : a.stacks 265 = table P encodeType)
    (hscopes : a.stacks 256 = SubexpIncidenceSlotProgram.scopeBits scopes)
    (hfactor : a.stacks 261 = unary e)
    (hsource : a.stacks 260 = key v) (htarget : a.stacks 262 = key w)
    (ha : HighClean a) :
    ∃ n ≤ 400 * (volume P encodeType v)^2 + 400 * (volume P encodeType w)^2 +
      27 * i.val + SubexpIncidenceSlotProgram.budget scopes e v.val + 30,
      ∃ b : Data, Eval classify n a b ∧ b.regs 5 = true ∧ b.regs 6 = false ∧
        b.stacks = Function.update
          (secondStore (firstStore a.stacks (.covered (unary i.val) (encodeType u)))
            (.covered (unary i.val) (encodeType y))) 284
          (unary (SubexpIncidenceSlotProgram.degree scopes e v.val + 1)) := by
  simpa only [volume, key, unary, List.length_replicate] using
    sameBlock_run a (records P encodeType) scopes e v.val w.val he
      (unary i.val) (encodeType u) (encodeType y)
      (lookup_covered P encodeType v i u hv) (lookup_covered P encodeType w i y hw)
      htable hscopes hfactor hsource htarget ha

/-- The physical one-based slot agrees with the canonical encounter-order
slot assignment. Its quadratic cost is derived from the actual prefix
selection and scan, including the input storage preserved by the caller. -/
theorem classify_typedSlot (P : PackingData (Fin D) U) (encodeType : U → Word)
    (Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (v w : Fin D) (e : SlotAssignment.Incident (Subexp.IncidencePlanSpec.pattern D scopes) v)
    (i : Fin P.blockCount) (u y : U)
    (hv : P.lookup v = some (i,u)) (hw : P.lookup w = some (i,y)) (a : Data)
    (htable : a.stacks 265 = table P encodeType)
    (hscopes : a.stacks 256 = SubexpIncidenceSlotProgram.scopeBits scopes)
    (hfactor : a.stacks 261 = unary e.val.val)
    (hsource : a.stacks 260 = key v) (htarget : a.stacks 262 = key w)
    (ha : HighClean a) :
    ∃ n ≤ 400 * (volume P encodeType v)^2 + 400 * (volume P encodeType w)^2 +
      27 * i.val + 1000 * ((SubexpIncidenceSlotProgram.scopeBits scopes).length +
        e.val.val + v.val + 1)^2 + 30,
      ∃ b : Data, Eval classify n a b ∧ b.regs 5 = true ∧ b.regs 6 = false ∧
        b.stacks 272 = encodeType u ∧ b.stacks 275 = encodeType y ∧
        b.stacks 284 = unary ((Subexp.IncidencePlanSpec.slots D Δ scopes hd v e).val + 1) ∧
        (∀ j : Fin 288, j ∉ cleanupPorts → b.stacks j = a.stacks j) := by
  obtain ⟨n, hn, b, he, h5, h6, hb⟩ := classify_sameBlock P encodeType v w i u y hv hw
    scopes e.val.val (Nat.le_of_lt e.val.isLt) a htable hscopes hfactor hsource htarget ha
  have hbound := SubexpIncidenceSlotProgram.budget_le scopes e.val.val v.val
    ((SubexpIncidenceSlotProgram.scopeBits scopes).length + e.val.val + v.val)
    (by omega) (by omega) (by omega)
  refine ⟨n, by omega, b, he, h5, h6, ?_, ?_, ?_, ?_⟩
  · rw [hb]
    simp [firstStore, secondStore, Subexp.GlobalBasisMetadata.Metadata.typeCode]
  · rw [hb]
    simp [secondStore, Subexp.GlobalBasisMetadata.Metadata.typeCode]
  · rw [hb]
    simp only [Function.update_same]
    rw [SubexpIncidenceSlotProgram.degree_eq_slot D Δ scopes hd v e]
  · intro j hj
    have h284 : j ≠ 284 := by intro h; subst j; exact hj (by decide)
    rw [hb, Function.update_of_ne h284,
      secondStore_frame _ _ j hj, firstStore_frame _ _ j hj]

end SubexponentialSAT.SubexpGlobalRowPacking

end OAI.Algorithms
