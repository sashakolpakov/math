import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceBankFrameInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceBankFrameBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceTables
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

namespace OAI.Algorithms

/-! Bind the actual integer-to-ring vector producer to the actual source-row
program. The coefficient table is obtained from its execution, not supplied
as an expanded table premise. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open IntegerRingLiftProgram
open RowSelectionProgram (WordPair pairValue pairLength)

theorem nativePositions_eq {r Q : ℕ} (u y : UniversalType r Q 1) :
    nativePositions u y=UniversalRowTableSource.positions
      (SubexpRowInterpolation.mismatchPositions (fun v => v.head) (u.slot 0) y) := by
  symm
  exact UniversalRowTableSource.positions_mismatch (fun v => v.head) (u.slot 0) y

theorem branch_length_le (a : Data) (rf : Fin 16 → Bool) (bits indices : List Bool)
    (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[]) (B : ℕ)
    (hB : ∀ j,(a.stacks j).length ≤ B) :
    ∀ j,((branchState a rf bits indices).stacks j).length ≤ B+bits.length+indices.length := by
  intro j
  simp only [branchState,stageTypes_stacks a h23 h24,Function.update_apply]
  split_ifs <;> first | omega | exact (hB _).trans (by omega)

theorem branch_emitterClean (a : Data) (rf : Fin 16 → Bool) (bits indices : List Bool)
    (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[]) (hc : EmitterClean a) :
    EmitterClean (branchState a rf bits indices) := by
  intro j hj hk hn
  have h23' : j≠23 := by intro h; subst j; norm_num at hj
  have h24' : j≠24 := by intro h; subst j; norm_num at hj
  have h67' : j≠67 := by intro h; subst j; norm_num at hj
  have h71' : j≠71 := by intro h; subst j; norm_num at hj
  simpa [branchState,stageTypes_stacks a h23 h24,h23',h24',h67',h71'] using hc j hj hk hn

/- Exact prepare/call/export/cleanup trace with actual generated model codes.
Only the already prepared arithmetic and node caches are inputs. -/
theorem native_universal_cleanup_eval {r Q d : ℕ}
    (Hwords : List (List Bool)) (width : List Bool) (power : WordPair)
    (as : List Bool) (R : ℕ) (start : Fin Q) (u y : UniversalType r Q 1)
    (hlen : Hwords.length=R) (hwords : ∀ x∈Hwords,x.length=width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat=
      (List.range R).map (LayoutCoefficientRecurrence.H as.length))
    (hp : pairValue power=(2:ℤ)^(R-1))
    (hpt : LayoutProgramScalar.wordTotal power=2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : as.length ≤ Q) (hQ : 1 ≤ Q)
    (t : ℕ) (ht : 0 < t) (hd : 0 < d) (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (zero one minusOne invDenom : ModelCode t d)
    (hzero : (RingProgram.modelRing t ht hd model M cache).decode zero=0)
    (hone : (RingProgram.modelRing t ht hd model M cache).decode one=1)
    (hminus : (RingProgram.modelRing t ht hd model M cache).decode minusOne= -1)
    (integerWord : ℤ → ModelCode t d)
    (hinteger : ∀ z,(RingProgram.modelRing t ht hd model M cache).decode (integerWord z)=
      (z:model.O t))
    (a : Data) (htemp : a.stacks 319=[]) (h23 : a.stacks 23=[]) (h24 : a.stacks 24=[])
    (ready : CachedReady t model M cache zero one minusOne
      (projectState id vectorPorts (Staging.result 0 1 stageTypesOps a)).stacks)
    (hinv : (projectState id vectorPorts (Staging.result 0 1 stageTypesOps a)).stacks 252=
      RingProgram.flat invDenom)
    (hinput : ∀ i,(projectState id vectorPorts (Staging.result 0 1 stageTypesOps a)).stacks
      (LayoutSourceValuesProgram.Native.numeratorPorts i)=
      (Numerator.state (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R as)
        (fun _=>false) start u y [] [] ([],[])).stacks i)
    (hq : (a.stacks 22).length=Q) (h37 : a.stacks 37=[])
    (h64 : a.stacks 64=[]) (h65 : a.stacks 65=[]) (h67 : a.stacks 67=[]) (h71 : a.stacks 71=[])
    (hc : EmitterClean a) (h274 : a.stacks 274=[])
    (h0 : a.stacks 0=[]) (h1 : a.stacks 1=[]) (h2 : a.stacks 2=[]) (h3 : a.stacks 3=[])
    (inverse negative : Fin Q → ModelCode t d) (difference : Fin Q → Fin Q → ModelCode t d)
    (ringWidth rowWidth : List Bool) (hringWidth : ringWidth.length=d*SubexpLiftRing.baseWidth 3 t)
    (hrowWidth : rowWidth.length=Q*ringWidth.length)
    (hi : a.stacks 308=(List.ofFn (fun i=>RingProgram.flat (inverse i))).flatten)
    (hn : a.stacks 309=(List.ofFn (fun i=>RingProgram.flat (negative i))).flatten)
    (hr : a.stacks 310=(List.ofFn (fun i=>
      (List.ofFn (fun j=>RingProgram.flat (difference i j))).flatten)).flatten)
    (hw : a.stacks 311=ringWidth) (hrw : a.stacks 312=rowWidth)
    (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B) :
    ∃ codes : Fin Q → ModelCode t d,
      (∀ node,(RingProgram.modelRing t ht hd model M cache).decode (codes node)=
        (RingProgram.modelRing t ht hd model M cache).decode
          (sourceValue (RingProgram.modelRing t ht hd model M cache).program
            integerWord invDenom as.length R u 0 y node)) ∧
      ∃ n ≤ Staging.cost 0 1 stageTypesOps a+
          LayoutSourceValuesProgram.Native.tableBudget as.length R width.length (pairLength power) t d u y+
          (UniversalRowMismatchTypes.extractBudget (r:=r) (Q:=Q) (0:Fin 1)+
            UniversalRowMismatchProgram.budget Q r+8*(Q*r)+13)+
          finishBound (SourceTyped.tables RingProgram.flat codes inverse negative difference)
            ringWidth rowWidth (nativePositions u y)
            (branchState a (fun _=>false) (List.ofFn (fun i=>RingProgram.flat (codes i))).flatten
              (nativeIndices u y))
            (B+Q*(d*SubexpLiftRing.baseWidth 3 t)+(nativeIndices u y).length),
        ∃ b : Data, Eval (.seq universal cleanup) n a b ∧
          b.stacks=Function.update (clearedStacks a) 287
            (UniversalRowProgram.rowCode (a.stacks 313) (a.stacks 314) (a.stacks 313++a.stacks 314)
              (UniversalRowDataProgram.row
                (SourceTyped.tables RingProgram.flat codes inverse negative difference)
                (nativePositions u y)
                (if a.stacks 289=a.stacks 292 then a.stacks 314 else a.stacks 313) (a.stacks 47))) := by
  let p := projectState id vectorPorts (Staging.result 0 1 stageTypesOps a)
  have hpfield (j : Fin 256) (hj23 : j≠23) (hj24 : j≠24) :
      p.stacks j=a.stacks (vectorPorts j) := by
    have hn23 : vectorPorts j≠23 := by
      intro h; apply hj23; apply vectorPorts_inj; exact h
    have hn24 : vectorPorts j≠24 := by
      intro h; apply hj24; apply vectorPorts_inj; exact h
    simp [p,projectState,stageTypes_stacks a h23 h24,hn23,hn24]
  obtain ⟨words,rv,hwlen,hwsize,hwvalid,nv,hnv,hvector⟩ :=
    LayoutSourceValuesProgram.Native.tableProgram_runsIn Hwords width power as R start u y
      hlen hwords hvalues hp hpt hwidth hAQ hQ t ht hd model M cache hz
      zero one minusOne invDenom hzero hone hminus p.stacks ready hinv hinput
      (by simpa [hpfield 22 (by decide) (by decide),vectorPorts] using hq)
      (by simpa [hpfield 37 (by decide) (by decide),vectorPorts] using h37)
      (by simpa [hpfield 64 (by decide) (by decide),vectorPorts] using h64)
      (by simpa [hpfield 65 (by decide) (by decide),vectorPorts] using h65)
      (by simpa [hpfield 67 (by decide) (by decide),vectorPorts] using h67) p.regs
  obtain ⟨codes,hcodes,hmeaning⟩ := LayoutSourceValuesProgram.Native.generated_source_codes
    as.length R t ht hd model M cache invDenom integerWord hinteger u y words hwlen hwvalid
  let tables := SourceTyped.tables RingProgram.flat codes inverse negative difference
  obtain ⟨nm,hnm,rm,hmismatch⟩ := native_mismatch_branch a
    (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R as) start u y
    words.flatten rv h23 h24 h71 hinput
  have hvalid : UniversalRowLoop.Valid tables ringWidth rowWidth (nativePositions u y) := by
    rw [nativePositions_eq]
    exact SourceTyped.tables_valid RingProgram.flat codes inverse negative difference ringWidth rowWidth
      (fun c=>(RingProgram.flat_length c).trans hringWidth.symm) hrowWidth _
  have hsize : words.flatten.length=Q*(d*SubexpLiftRing.baseWidth 3 t) := by
    rw [List.length_flatten]
    have hmap : words.map List.length=List.replicate words.length (d*SubexpLiftRing.baseWidth 3 t) :=
      List.map_eq_replicate_iff.mpr hwsize
    simp only [hmap,List.sum_replicate,hwlen,smul_eq_mul]
  have hzfield (j : Fin 320) (hj23 : j≠23) (hj24 : j≠24) (hj67 : j≠67) (hj71 : j≠71) :
      (branchState a rm words.flatten (nativeIndices u y)).stacks j=a.stacks j := by
    simp [branchState,stageTypes_stacks a h23 h24,hj23,hj24,hj67,hj71]
  obtain ⟨n,hnfinal,b,he,hbs⟩ := universal_cleanup_eval a htemp h23 h24 words.flatten
    (nativeIndices u y) rv rm nv nm hvector hmismatch tables ringWidth rowWidth (nativePositions u y)
    hvalid (branch_emitterClean a rm _ _ h23 h24 hc)
    (by simpa [hzfield 274 (by decide) (by decide) (by decide) (by decide)] using h274)
    (by simpa [hzfield 0 (by decide) (by decide) (by decide) (by decide)] using h0)
    (by simpa [hzfield 1 (by decide) (by decide) (by decide) (by decide)] using h1)
    (by simpa [hzfield 2 (by decide) (by decide) (by decide) (by decide)] using h2)
    (by simpa [hzfield 3 (by decide) (by decide) (by decide) (by decide)] using h3)
    (by simp [tables,SourceTyped.tables,hcodes]) hi hn
    (by
      rw [hr]
      simp [tables, SourceTyped.tables, UniversalRowLoop.Tables.rows]
      rfl)
    (nativeIndices_eq u y) hw hrw (B+Q*(d*SubexpLiftRing.baseWidth 3 t)+(nativeIndices u y).length)
    (by simpa only [hsize] using branch_length_le a rm words.flatten (nativeIndices u y) h23 h24 B hB)
  refine ⟨codes,hmeaning,n,?_,b,he,?_⟩
  · have hwordsflat := congrArg List.flatten hcodes
    rw [hwordsflat] at hnfinal
    have hfinish : finishBound tables ringWidth rowWidth (nativePositions u y)
        (branchState a rm (List.ofFn (fun node => RingProgram.flat (codes node))).flatten
          (nativeIndices u y))
        (B+Q*(d*SubexpLiftRing.baseWidth 3 t)+(nativeIndices u y).length) =
      finishBound (SourceTyped.tables RingProgram.flat codes inverse negative difference)
        ringWidth rowWidth (nativePositions u y)
        (branchState a (fun _ => false) (List.ofFn (fun node => RingProgram.flat (codes node))).flatten
          (nativeIndices u y))
        (B+Q*(d*SubexpLiftRing.baseWidth 3 t)+(nativeIndices u y).length) := rfl
    rw [hfinish] at hnfinal
    omega
  · simpa only [branch_sourceWord a rm words.flatten (nativeIndices u y) h23 h24 tables (nativePositions u y)] using hbs

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
