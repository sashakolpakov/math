import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceConfiguration
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceBankFrameNative

namespace OAI.Algorithms

/-! The universal branch has a concrete trace and a typed polynomial witness.
The only table used below is returned by the actual native vector program. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open IntegerRingLiftProgram RowSelectionProgram

variable {r Q d : ℕ}

def nativeBudget (p : Parameters r Q d) (S : ℕ) (a : Data)
    (codes : Fin Q → ModelCode p.t d) (u y : UniversalType r Q 1) : ℕ :=
  Staging.cost 0 1 stageTypesOps a+
  LayoutSourceValuesProgram.Native.tableBudget p.aWord.length p.R p.width.length
    (pairLength p.power) p.t d u y+
  (UniversalRowMismatchTypes.extractBudget (r:=r) (Q:=Q) (0:Fin 1)+
    UniversalRowMismatchProgram.budget Q r+8*(Q*r)+13)+
  finishBound (SourceTyped.tables RingProgram.flat codes p.inverse p.negative p.difference)
    p.ringWidth p.rowWidth (nativePositions u y)
    (branchState a (fun _=>false) (List.ofFn (fun i=>RingProgram.flat (codes i))).flatten
      (nativeIndices u y))
    (S+Q*(d*SubexpLiftRing.baseWidth 3 p.t)+(nativeIndices u y).length)

theorem universal_generated (p : Parameters r Q d) (a : Data) (ha : Ready p a)
    (u y : UniversalType r Q 1)
    (hu : a.stacks 289=CollisionProgram.encodeType u)
    (hy : a.stacks 292=CollisionProgram.encodeType y)
    (S : ℕ) (hS : ∀ j,(a.stacks j).length ≤ S)
    (hQ : Q ≤ S) (hR : p.R ≤ S)
    (hW : p.ringWidth.length ≤ S) (hRW : p.rowWidth.length ≤ S) :
    ∃ codes : Fin Q → ModelCode p.t d, ∃ n ≤ nativeBudget p S a codes u y,
      ∃ b : Data, ∃ bytes : List Bool,
        Eval (.seq universal cleanup) n a b ∧
        b.stacks=Function.update (clearedStacks a) 287 bytes ∧
        SourceWitness.Generated p.ops p.R (UniversalRowSourceBound.sourceLengthBound S)
          (p.rows u y) bytes := by
  have h23 : a.stacks 23=[] := ha.work.work 23 (by decide) (Or.inl (by decide))
  have h24 : a.stacks 24=[] := ha.work.work 24 (by decide) (Or.inl (by decide))
  have h67 : a.stacks 67=[] := ha.work.work 67 (by decide) (Or.inl (by decide))
  have h71 : a.stacks 71=[] := ha.work.work 71 (by decide) (Or.inl (by decide))
  have h274 : a.stacks 274=[] := ha.work.work 274 (by decide) (Or.inl (by decide))
  have hready := cachedReady_stage p.t p.model p.modulus p.cache _ _ _ a ha.ring h23 h24
  have hinv : (projectState id vectorPorts (Staging.result 0 1 stageTypesOps a)).stacks 252=
      RingProgram.flat p.invDenom := by
    change lowStore (Staging.result 0 1 stageTypesOps a) 252=_
    rw [stageTypes_lowStore a h23 h24 252 (by decide) (by decide)]
    exact ha.inverseDenominator
  obtain ⟨codes,hcodes,n,hn,b,he,hbs⟩ := native_universal_cleanup_eval
    p.hwords p.width p.power p.aWord p.R p.start u y p.hlen p.hwidths p.hvalues
    p.hp p.hpt p.hwidth p.hAQ p.hQ p.t p.ht p.hd p.model p.modulus p.cache p.hz
    p.ops.zeroRun.1 p.ops.oneRun.1 p.minusOne p.invDenom
    p.ops.zero_correct p.ops.one_correct p.hminus p.integerWord p.hinteger a
    ha.work.temp h23 h24 hready hinv
    (inputFields_stage a p.saved p.start u y (ha.input u y) h23 h24 hu hy)
    ha.nodes ha.work.count ha.work.tableCount ha.work.tableAccum h67 h71
    ha.work.emitter h274 (ha.work.low 0 (by decide)) (ha.work.low 1 (by decide))
    (ha.work.low 2 (by decide)) (ha.work.low 3 (by decide))
    p.inverse p.negative p.difference p.ringWidth p.rowWidth p.hringWidth p.hrowWidth
    ha.inverses ha.negatives ha.differences ha.ringWidth ha.rowWidth S hS
  let delta : ModelCode p.t d := if u=y then p.ops.oneRun.1 else p.ops.zeroRun.1
  let bytes := UniversalRowProgram.rowCode (RingProgram.flat p.ops.zeroRun.1)
    (RingProgram.flat p.ops.oneRun.1) (RingProgram.flat p.ops.zeroRun.1++RingProgram.flat p.ops.oneRun.1)
    (UniversalRowDataProgram.row (SourceTyped.tables RingProgram.flat codes p.inverse p.negative p.difference)
      (UniversalRowTableSource.positions (SubexpRowInterpolation.mismatchPositions (fun v=>v.head) (u.slot 0) y))
      (RingProgram.flat delta) (a.stacks 47))
  have hb : b.stacks=Function.update (clearedStacks a) 287 bytes := by
    by_cases heq : u=y <;>
      simpa [bytes,delta,ha.zero,ha.one,hu,hy,nativePositions_eq,heq] using hbs
  have hbase : 0 < SubexpLiftRing.baseWidth 3 p.t := by
    rw [RingProgram.ternary_baseWidth]
    have := p.ht
    omega
  have hg := SourceWitness.universal p.ops hbase p.nodeCache p.integerWord p.hinteger
    p.denom p.invDenom p.hinv (p.model.nodeUnits p.t Q p.ht p.hfield)
    (SourceCache.native_node p.t p.ht p.hd p.model p.modulus p.cache p.minusOne p.hfield)
    (SourceCache.native_inverse p.t p.ht p.hd p.model p.modulus p.cache p.minusOne p.hminus p.hfield)
    (SourceCache.native_difference p.t p.ht p.hd p.model p.modulus p.cache p.minusOne p.hminus p.hfield)
    codes p.inverse p.negative p.difference p.aWord.length p.R u y delta (a.stacks 47)
    hcodes (fun _=>rfl)
    (SourceCache.native_negative p.t p.ht p.hd p.model p.modulus p.cache p.minusOne p.hminus)
    (fun _ _=>rfl) (by rfl) ha.limit p.ringWidth p.rowWidth p.hringWidth p.hrowWidth
    S hQ hW hRW hR
  exact ⟨codes,n,hn,b,bytes,he,hb,hg⟩

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
