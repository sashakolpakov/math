import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceBankCost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceDispatch
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramBlockCode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpressionBounds

namespace OAI.Algorithms

/-! Complete packed source dispatch from actual metadata. All possible
branches execute native commands and return an exact typed compiler source. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking IntegerRingLiftProgram RowSelectionProgram

variable {r Q d D : ℕ}

def metadataRecords (P : PackingData (Fin D) (UniversalType r Q 1)) :=
  PackingMetadata.records P (fun v=>List.replicate v.val true) CollisionProgram.encodeType

def lookupBudget (P : PackingData (Fin D) (UniversalType r Q 1)) (row col : Fin D) : ℕ :=
  400*(GlobalBasisMetadata.volume (metadataRecords P) (List.replicate row.val true))^2+
  400*(GlobalBasisMetadata.volume (metadataRecords P) (List.replicate col.val true))^2+1

private theorem unary_inj {x y : Fin D} :
    List.replicate x.val true=List.replicate y.val true ↔ x=y := by
  constructor
  · intro h; apply Fin.ext; simpa using congrArg List.length h
  · rintro rfl; rfl

theorem command_eval (p : Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1)) (row col : Fin D)
    (a : Data) (ha : Ready p a) (S : ℕ)
    (hclean : ∀ j∈cleanupPorts,a.stacks j=[])
    (hmeta : a.stacks 306=SelectorProgram.rawRecords (metadataRecords P))
    (hrow : a.stacks 304=List.replicate row.val true)
    (hcol : a.stacks 305=List.replicate col.val true)
    (hsize : ∀ j,(a.stacks j).length ≤ S)
    (hmetadata : ∀ v,MetadataBound (PackingMetadata.value P CollisionProgram.encodeType v) S)
    (hQ : Q ≤ S) (hR : p.R ≤ S) (hW : p.ringWidth.length ≤ S) (hRW : p.rowWidth.length ≤ S) :
    ∃ n ≤ lookupBudget P row col+uniformBudget p S+200*S+300,
      ∃ b : Data, ∃ bytes : List Bool, Eval command n a b ∧
        b.stacks=Function.update a.stacks 287 bytes ∧
        SourceWitness.Generated p.ops p.R (UniversalRowSourceBound.sourceLengthBound S)
          (packedValue P p.rows row col) bytes := by
  let mr := PackingMetadata.value P CollisionProgram.encodeType row
  let mc := PackingMetadata.value P CollisionProgram.encodeType col
  have hkey : Function.Injective (fun v : Fin D=>List.replicate v.val true) := by
    intro x y h; exact unary_inj.mp h
  obtain ⟨nl,hnl,b,hl,hbs,h4,h5⟩ := lookup_eval a (metadataRecords P)
    (List.replicate row.val true) (List.replicate col.val true) mr mc
    (PackingMetadata.lookup_eq P _ _ hkey row) (PackingMetadata.lookup_eq P _ _ hkey col)
    hmeta hrow hcol (lookup_ready hclean)
  change nl ≤ lookupBudget P row col at hnl
  have hbready := ha.metadata mr mc hbs
  have hbsize := metadata_length mr mc S hbs hsize (hmetadata row) (hmetadata col)
  have hbclear := cleared_metadata_eq mr mc hclean hbs
  have hbLit : LiteralReady b := hbready.work.literal
  have hbCmp : CompareReady b := hbready.work.compare
  have hzlen := LayoutSourceExpression.literal_length_le_sourceLengthBound p.ops.zeroRun.1
    (p.hringWidth ▸ hW)
  have holen := LayoutSourceExpression.literal_length_le_sourceLengthBound p.ops.oneRun.1
    (p.hringWidth ▸ hW)
  have hzero := SourceWitness.literal_zero p.ops p.R _ hzlen
  have hone := SourceWitness.literal_one p.ops p.R _ holen
  cases hv : P.lookup row with
  | none =>
    have hb4 : b.regs 4=false := by
      simpa [mr,PackingMetadata.value,hv,GlobalBasisMetadata.Metadata.coveredFlag] using h4
    obtain ⟨nu,hnu,z,hu,hzs⟩ := uncovered_cleanup b hbLit hbCmp S hbsize
    have hs := selected_attach (coveredFlag:=false) hb4 hu
    have hbr : b.stacks 304=List.replicate row.val true := by
      rw [hbs,metadata_frame a mr mc 304 (Or.inr (by decide))]; exact hrow
    have hbc : b.stacks 305=List.replicate col.val true := by
      rw [hbs,metadata_frame a mr mc 305 (Or.inr (by decide))]; exact hcol
    let bytes := SubexpKernelControl.pushWord
      (if row=col then RingProgram.flat p.ops.oneRun.1 else RingProgram.flat p.ops.zeroRun.1)
    refine ⟨nl+(nu+1),by omega,z,bytes,hl.seq hs,?_,?_⟩
    · simpa only [hbclear,hbr,hbc,unary_inj,hbready.one,hbready.zero] using hzs
    · by_cases heq : row=col
      · subst col
        simpa [bytes,packedValue,hv] using hone
      · simpa [bytes,packedValue,hv,heq,eq_comm] using hzero
  | some z =>
    rcases z with ⟨j,u⟩
    have hb4 : b.regs 4=true := by
      simpa [mr,PackingMetadata.value,hv,GlobalBasisMetadata.Metadata.coveredFlag] using h4
    cases hw : P.lookup col with
    | none =>
      have hb5 : b.regs 5=false := by
        simpa [mc,PackingMetadata.value,hw,GlobalBasisMetadata.Metadata.coveredFlag] using h5
      obtain ⟨nu,hnu,z,hu,hzs⟩ := covered_uncovered_cleanup b hbLit hb5 S hbsize
      have hs := selected_attach (coveredFlag:=true) hb4 hu
      refine ⟨nl+(nu+1),by omega,z,SubexpKernelControl.pushWord (RingProgram.flat p.ops.zeroRun.1),hl.seq hs,?_,?_⟩
      · simpa only [hbclear,hbready.zero] using hzs
      · simpa only [packedValue,hv,hw] using hzero
    | some z =>
      rcases z with ⟨k,y⟩
      have hb5 : b.regs 5=true := by
        simpa [mc,PackingMetadata.value,hw,GlobalBasisMetadata.Metadata.coveredFlag] using h5
      have hbu : b.stacks 289=CollisionProgram.encodeType u := by
        simp [hbs,metadataStacks,mr,PackingMetadata.value,hv,GlobalBasisMetadata.Metadata.typeCode]
      have hby : b.stacks 292=CollisionProgram.encodeType y := by
        simp [hbs,metadataStacks,mc,PackingMetadata.value,hw,GlobalBasisMetadata.Metadata.typeCode]
      have hblock : b.stacks 288=b.stacks 291 ↔ j=k := by
        simp [hbs,metadataStacks,mr,mc,PackingMetadata.value,hv,hw,
          GlobalBasisMetadata.Metadata.block,PackingMetadata.unary,Fin.val_inj]
      obtain ⟨nc,hnc,m,hcmp,hms,_,h7⟩ := compareBlocks_eval b hbCmp.1 hbCmp.2.1 hbCmp.2.2.1 hbCmp.2.2.2
      have hmready := hbready.frame hms
      have hmsize : ∀ i,(m.stacks i).length ≤ S := by simpa only [hms] using hbsize
      have hmclear : clearedStacks m=a.stacks := (cleared_eq_of_stacks hms).trans hbclear
      have hnc' : nc ≤ 27*S+32 := by have h1:=hbsize 288; have h2:=hbsize 291; omega
      by_cases heq : j=k
      · have hm7 : m.regs 7=true := by simp [h7,hblock,heq]
        obtain ⟨codes,nu,hnu,z,bytes,hu,hzs,hgen⟩ := universal_generated p m hmready u y
          (by simpa only [hms] using hbu) (by simpa only [hms] using hby) S hmsize hQ hR hW hRW
        have hbound := (nativeBudget_le p S m codes u y
          (hmready.work.work 23 (by decide) (Or.inl (by decide)))
          (hmready.work.work 24 (by decide) (Or.inl (by decide))) hmsize hQ hW hRW).trans
          (universalBudget_le p S u y)
        have hs := selected_attach (coveredFlag:=true) hb4 (covered_attach hcmp hb5 hm7 hu)
        refine ⟨nl+(nc+nu+2+1),by omega,z,bytes,hl.seq hs,?_,?_⟩
        · simpa only [hmclear] using hzs
        · simpa only [packedValue,hv,hw,ite_eq_left heq] using hgen
      · have hm7 : m.regs 7=false := by simp [h7,hblock,heq]
        obtain ⟨nu,hnu,z,hu,hzs⟩ := literal_cleanup_eval 313 (Or.inl rfl) m
          hmready.work.temp hmready.work.literal.2.1 hmready.work.literal.2.2.1
          hmready.work.output S hmsize
        cases hu with
        | seq hli hcl =>
          have hc := (Eval.ite_true (no:=zero) hb5
            (hcmp.seq (Eval.ite_false (yes:=universal) hm7 hli))).seq hcl
          have hs := selected_attach (coveredFlag:=true) hb4 hc
          have h313 := hmsize 313
          refine ⟨_,by omega,z,SubexpKernelControl.pushWord (RingProgram.flat p.ops.zeroRun.1),hl.seq hs,?_,?_⟩
          · simpa only [hmclear,hmready.zero] using hzs
          · simpa only [packedValue,hv,hw,ite_eq_right heq] using hzero

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
