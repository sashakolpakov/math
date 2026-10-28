import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramEntryBankCovered
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramDispatch

namespace OAI.Algorithms

/-! A native entry of the all-incidence integer matrix. The actual packing
metadata is read twice; no precomputed integer matrix is supplied. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking RowSelectionProgram

variable {r Q D : ℕ}

def metadataRecords (P : PackingData (Fin D) (UniversalType r Q 1)) :=
  PackingMetadata.records P (fun v => List.replicate v.val true) CollisionProgram.encodeType

def lookupBudget (P : PackingData (Fin D) (UniversalType r Q 1)) (row col : Fin D) : ℕ :=
  400*(GlobalBasisMetadata.volume (metadataRecords P) (List.replicate row.val true))^2+
  400*(GlobalBasisMetadata.volume (metadataRecords P) (List.replicate col.val true))^2+1

private theorem unary_inj {x y : Fin D} :
    List.replicate x.val true=List.replicate y.val true ↔ x=y := by
  constructor
  · intro h; apply Fin.ext; simpa using congrArg List.length h
  · rintro rfl; rfl

private theorem constraintMassBound_one (Q R : ℕ) : 1 ≤ constraintMassBound Q R := by
  have hh : 0 < 2^(R-1) := by positivity
  unfold constraintMassBound
  omega

/-- The callback consumed by the owner-fiber loop. `K` and `L` are numerical
upper bounds on the closed universal program, not program-service premises. -/
theorem command_eval (P : PackingData (Fin D) (UniversalType r Q 1))
    (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (aWord : List Bool) (R : ℕ) (t : Fin Q) (row col : Fin D)
    (a : Data) (S K L : ℕ)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H aWord.length))
    (hp : pairValue power=(2:ℤ)^(R-1)) (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hpos : BinaryArithmetic.toNat power.1=2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : aWord.length ≤ Q) (hQ : 1 ≤ Q)
    (hc : CacheWords (r:=r) a (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R aWord) t)
    (hready : BaseReady a)
    (hmeta : a.stacks 200=SelectorProgram.rawRecords (metadataRecords P))
    (hrow : a.stacks 252=List.replicate row.val true)
    (hcol : a.stacks 253=List.replicate col.val true)
    (hsize : ∀ j : Fin 256,j.val < 212 → (a.stacks j).length ≤ S)
    (hrs : row.val ≤ S) (hcs : col.val ≤ S)
    (hmetadata : ∀ v, MetadataBound (PackingMetadata.value P CollisionProgram.encodeType v) S)
    (hK : ∀ u y : UniversalType r Q 1, IntegerEntry.budget aWord.length R width.length (pairLength power) power.1.length t u y ≤ K)
    (hL : ∀ u y : UniversalType r Q 1, IntegerEntry.lengthBound R width.length (pairLength power) u y+power.1.length+1 ≤ L)
    (hL1 : 1 ≤ L) :
    ∃ n ≤ lookupBudget P row col+K+550*S+450*L+1200, ∃ rf result,
      Eval command n a (finish a rf result) ∧
      pairValue result=localEntry P aWord.length R t row col ∧
      LayoutProgramScalar.wordTotal result ≤ constraintMassBound Q R ∧ pairLength result ≤ L := by
  let mr := PackingMetadata.value P CollisionProgram.encodeType row
  let mc := PackingMetadata.value P CollisionProgram.encodeType col
  have hkey : Function.Injective (fun v : Fin D => List.replicate v.val true) := by
    intro x y h; exact unary_inj.mp h
  obtain ⟨nl,hnl,b,hl,hbs,h4,h5⟩ := lookup_eval a (metadataRecords P)
    (List.replicate row.val true) (List.replicate col.val true) mr mc
    (PackingMetadata.lookup_eq P _ _ hkey row)
    (PackingMetadata.lookup_eq P _ _ hkey col) hmeta hrow hcol
    (fun j hj hk => hready.1 j (by omega))
  change nl ≤ lookupBudget P row col at hnl
  have hbready : MetadataReady b := metadata_ready mr mc hready hbs
  have hbhigh := metadata_high mr mc hbs
  have hb254 : b.stacks 254=[] := (hbhigh _ (by decide)).trans hready.2.1
  have hb255 : b.stacks 255=[] := (hbhigh _ (by decide)).trans hready.2.2
  have hbsize := metadata_length mr mc S hbs hsize (hmetadata row) (hmetadata col)
  have hbfields := metadata_fields_le hbsize
  have hbcache := hc.frame hbhigh
  have hbrow : b.stacks 252=List.replicate row.val true := (hbhigh _ (by decide)).trans hrow
  have hbcol : b.stacks 253=List.replicate col.val true := (hbhigh _ (by decide)).trans hcol
  cases hv : P.lookup row with
  | none =>
    have hb4 : b.regs 4=false := by
      simpa [mr,PackingMetadata.value,hv,GlobalBasisMetadata.Metadata.coveredFlag] using h4
    obtain ⟨nu,hnu,z,hu,hzs⟩ := uncovered_cleanup_eval b hbready hb254
    let result : WordPair := (if row=col then [true] else [],[])
    have hkeys : b.stacks 252=b.stacks 253 ↔ row=col := by rw [hbrow,hbcol]; exact unary_inj
    have hz : z=finish b z.regs result := by
      apply congrArg₂ StructuredProgram.State.mk rfl
      funext j
      rw [hzs j]
      simp only [result]
      by_cases h255 : j=255
      · subst j; simp [hb255]
      · simp [h255,hkeys]
    rw [hz,finish_frame z.regs result hbhigh] at hu
    have hs := selected_attach (coveredFlag:=false) hb4 hu
    have ht := hl.seq hs
    refine ⟨nl+(nu+1),?_,z.regs,result,ht,?_,?_,?_⟩
    · simp only [hbrow,hbcol,List.length_replicate] at hnu
      omega
    · by_cases heq : row=col
      · subst col
        simp [result,pairValue,RowSelectionProgram.signedValue,localEntry,hv]
      · simp [result,pairValue,RowSelectionProgram.signedValue,localEntry,hv,heq,eq_comm]
    · have hone := constraintMassBound_one Q R
      by_cases heq : row=col <;> simp [result,heq,LayoutProgramScalar.wordTotal,pairTotal] ; omega
    · by_cases heq : row=col <;> simp [result,heq,pairLength] ; omega
  | some z =>
    rcases z with ⟨j,u⟩
    have hb4 : b.regs 4=true := by
      simpa [mr,PackingMetadata.value,hv,GlobalBasisMetadata.Metadata.coveredFlag] using h4
    cases hw : P.lookup col with
    | none =>
      have hb5 : b.regs 5=false := by
        simpa [mc,PackingMetadata.value,hw,GlobalBasisMetadata.Metadata.coveredFlag] using h5
      obtain ⟨nu,hnu,rf,hu⟩ := covered_uncovered_eval b hbready hb254 hb255 hb5
      rw [finish_frame rf ([],[]) hbhigh] at hu
      have hs := selected_attach (coveredFlag:=true) hb4 hu
      refine ⟨nl+(nu+1),by omega,rf,([],[]),hl.seq hs,?_,?_,?_⟩
      · simp [pairValue,RowSelectionProgram.signedValue,localEntry,hv,hw]
      · simp [LayoutProgramScalar.wordTotal,pairTotal]
      · simp [pairLength]
    | some z =>
      rcases z with ⟨k,y⟩
      have hb5 : b.regs 5=true := by
        simpa [mc,PackingMetadata.value,hw,GlobalBasisMetadata.Metadata.coveredFlag] using h5
      have hbu : b.stacks 65=CollisionProgram.encodeType u := by
        simp [hbs,metadataStacks,mr,PackingMetadata.value,hv,GlobalBasisMetadata.Metadata.typeCode]
      have hby : b.stacks 68=CollisionProgram.encodeType y := by
        simp [hbs,metadataStacks,mc,PackingMetadata.value,hw,GlobalBasisMetadata.Metadata.typeCode]
      have hbblock : b.stacks 64=b.stacks 67 ↔ j=k := by
        simp only [hbs,metadataStacks,Function.update_apply]
        simp [mr,mc,PackingMetadata.value,hv,hw,GlobalBasisMetadata.Metadata.block,
          PackingMetadata.unary,Fin.val_inj]
      obtain ⟨nu,hnu,rf,result,hu,hvresult,hmresult,hlresult⟩ := covered_eval Hwords width power aWord R t u y
        b S K L hlen hwords hvalues hp hpt hpos hwidth hAQ hQ hbcache hbready hb254 hb255
        hbu hby hb5 hbsize (hK u y) (hL u y)
      rw [finish_frame rf result hbhigh] at hu
      have hs := selected_attach (coveredFlag:=true) hb4 hu
      refine ⟨nl+(nu+1),by omega,rf,result,hl.seq hs,?_,hmresult,hlresult⟩
      rw [hvresult]
      by_cases heq : j=k <;>
        by_cases ha : MatrixExtendedEntryProgram.anchorValid (0:Fin 1) t u y <;>
        simp [localEntry,hv,hw,IntegerEntry.value,heq,ha,hbblock]

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
