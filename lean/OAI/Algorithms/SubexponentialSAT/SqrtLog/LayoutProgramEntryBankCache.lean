import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramEntryBankInner
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramEntryBankFrameUncovered

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {r Q : ℕ}

/-- The persistent cache fields. There is deliberately no condition on the
caller's private accumulator and queue ports212..251. -/
structure CacheWords (a : Data) (c : Numerator.Saved) (t : Fin Q) : Prop where
  hp : a.stacks 202=c.hp
  hn : a.stacks 203=c.hn
  hw : a.stacks 204=c.width
  hpos : a.stacks 205=c.power.1
  hneg : c.power.2=[]
  hr : a.stacks 206=c.r
  ha : a.stacks 207=c.a
  colors : a.stacks 208=List.replicate r true
  nodes : a.stacks 209=List.replicate Q true
  node : a.stacks 210=List.replicate t.val true
  typeWidth : a.stacks 211=List.replicate (Q*r) true

theorem CacheWords.frame {a b : Data} {c : Numerator.Saved} {t : Fin Q}
    (h : CacheWords (r:=r) a c t)
    (hf : ∀ j : Fin 256, 200 ≤ j.val → b.stacks j=a.stacks j) : CacheWords (r:=r) b c t := by
  constructor
  · exact (hf _ (by decide)).trans h.hp
  · exact (hf _ (by decide)).trans h.hn
  · exact (hf _ (by decide)).trans h.hw
  · exact (hf _ (by decide)).trans h.hpos
  · exact h.hneg
  · exact (hf _ (by decide)).trans h.hr
  · exact (hf _ (by decide)).trans h.ha
  · exact (hf _ (by decide)).trans h.colors
  · exact (hf _ (by decide)).trans h.nodes
  · exact (hf _ (by decide)).trans h.node
  · exact (hf _ (by decide)).trans h.typeWidth

theorem CacheWords.cached {a : Data} {c : Numerator.Saved} {t : Fin Q}
    (h : CacheWords (r:=r) a c t) (u y : UniversalType r Q 1)
    (hl : MetadataReady a) (hp : a.stacks 254=[]) (hn : a.stacks 255=[])
    (hu : a.stacks 65=CollisionProgram.encodeType u)
    (hy : a.stacks 68=CollisionProgram.encodeType y) : Cached a c t u y := by
  exact ⟨fun j hj => hl j (by omega) (Or.inl hj),
    hl 199 (by decide) (Or.inr (by decide)),hp,hn,h.hp,h.hn,h.hw,h.hpos,h.hneg,h.hr,h.ha,
    h.colors,h.nodes,h.node,h.typeWidth,hu,hy⟩

theorem metadata_ready {a b : Data} (mr mc : GlobalBasisMetadata.Metadata)
    (ha : BaseReady a) (hb : b.stacks=metadataStacks a mr mc) : MetadataReady b := by
  intro j hj hk
  rw [hb,metadataStacks_frame a mr mc j hk]
  exact ha.1 j hj

theorem metadata_high {a b : Data} (mr mc : GlobalBasisMetadata.Metadata)
    (hb : b.stacks=metadataStacks a mr mc) :
    ∀ j : Fin 256,200 ≤ j.val → b.stacks j=a.stacks j := by
  intro j hj
  rw [hb,metadataStacks_frame a mr mc j (Or.inr (by omega))]

def MetadataBound (m : GlobalBasisMetadata.Metadata) (S : ℕ) : Prop :=
  m.block.length ≤ S ∧ m.typeCode.length ≤ S ∧ m.rank.length ≤ S

theorem metadata_length {a b : Data} (mr mc : GlobalBasisMetadata.Metadata) (S : ℕ)
    (hb : b.stacks=metadataStacks a mr mc)
    (ha : ∀ j : Fin 256,j.val < 212 → (a.stacks j).length ≤ S)
    (hr : MetadataBound mr S) (hc : MetadataBound mc S) :
    ∀ j : Fin 256,j.val < 212 → (b.stacks j).length ≤ S := by
  intro j hj
  rw [hb]
  simp only [metadataStacks,Function.update_apply]
  split_ifs <;> first
    | exact hr.1
    | exact hr.2.1
    | exact hr.2.2
    | exact hc.1
    | exact hc.2.1
    | exact hc.2.2
    | exact ha j hj

theorem metadata_fields_le {a : Data} {S : ℕ}
    (h : ∀ j : Fin 256,j.val < 212 → (a.stacks j).length ≤ S) :
    metadataFieldsLength a ≤ 6*S := by
  have h1 := h 64 (by decide)
  have h2 := h 65 (by decide)
  have h3 := h 66 (by decide)
  have h4 := h 67 (by decide)
  have h5 := h 68 (by decide)
  have h6 := h 69 (by decide)
  rw [metadataFieldsLength_eq]
  omega

theorem finish_frame {a b : Data} (regs : Fin 16 → Bool) (result : RowSelectionProgram.WordPair)
    (hf : ∀ j : Fin 256,200 ≤ j.val → b.stacks j=a.stacks j) :
    finish b regs result=finish a regs result := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext j
  by_cases hj : j.val < 200
  · simp [hj]
  · simp only [ite_eq_right hj]
    rw [hf j (by omega)]

/-- Reattach the two covered-case branches around an actual inner trace. -/
theorem covered_attach {a b z : Data} {nc ni : ℕ}
    (hc : Eval compareBlocks nc a b) (h5 : a.regs 5=true) (h7 : b.regs 7=true)
    (hi : Eval inner ni b z) :
    Eval (.seq covered cleanup) (nc+ni+2) a z := by
  cases hi with
  | seq hp hi =>
    cases hi with
    | seq hi he =>
      cases he with
      | seq he hz =>
        have hh := (Eval.ite_true (no := (.base .skip : Code)) h5
          (hc.seq (Eval.ite_true (no := (.base .skip : Code)) h7 (hp.seq (hi.seq he))))).seq hz
        convert hh using 1 <;> (try simp [covered]) ; omega

/-- Reattach the row-covered flag after either concrete branch has run. -/
theorem selected_attach {a z : Data} {n : ℕ} {coveredFlag : Bool}
    (hf : a.regs 4=coveredFlag)
    (he : Eval (.seq (if coveredFlag then covered else uncovered) cleanup) n a z) :
    Eval (.seq (.ite 4 covered uncovered) cleanup) (n+1) a z := by
  cases coveredFlag
  · simp only [Bool.false_eq_true,ite_false] at he
    cases he with
    | seq h hclean =>
      simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
        (Eval.ite_false (yes:=covered) hf h).seq hclean
  · simp only [ite_true] at he
    cases he with
    | seq h hclean =>
      simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
        (Eval.ite_true (no:=uncovered) hf h).seq hclean

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
