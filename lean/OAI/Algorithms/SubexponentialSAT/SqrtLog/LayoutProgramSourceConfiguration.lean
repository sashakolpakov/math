import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceBankState
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceWitness
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceCache

namespace OAI.Algorithms

/-! Concrete numerical and cache inputs to the source bank. The state predicate
contains byte representations only; it contains no program-service premise. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open IntegerRingLiftProgram RowSelectionProgram

structure Parameters (r Q d : ℕ) where
  t : ℕ
  ht : 0 < t
  hd : 0 < d
  model : RingModel.Data d
  modulus : SubexpPreparedQuartic.Modulus 3 t
  cache : RingProgram.ScalarCache 3 t
  hz : BinaryArithmetic.toNat cache.zero.val < 3^t
  R : ℕ
  hwords : List (List Bool)
  width : List Bool
  power : WordPair
  aWord : List Bool
  hlen : hwords.length=R
  hwidths : ∀ x∈hwords,x.length=width.length
  hvalues : hwords.map BinaryArithmetic.toNat=(List.range R).map (LayoutCoefficientRecurrence.H aWord.length)
  hp : pairValue power=(2:ℤ)^(R-1)
  hpt : LayoutProgramScalar.wordTotal power=2^(R-1)
  hwidth : Q+1 ≤ width.length
  hAQ : aWord.length ≤ Q
  hQ : 1 ≤ Q
  hfield : Q < 3^d
  minusOne : ModelCode t d
  hminus : (RingProgram.modelRing t ht hd model modulus cache).decode minusOne= -1
  invDenom : ModelCode t d
  denom : (model.O t)ˣ
  hdenom : (denom : model.O t)=(LayoutNumerator.denominator R : model.O t)
  hinv : (RingProgram.modelRing t ht hd model modulus cache).decode invDenom=(↑(denom⁻¹):model.O t)
  integerWord : ℤ → ModelCode t d
  hinteger : ∀ z,(RingProgram.modelRing t ht hd model modulus cache).decode (integerWord z)=(z:model.O t)
  ringWidth : List Bool
  rowWidth : List Bool
  hringWidth : ringWidth.length=d*SubexpLiftRing.baseWidth 3 t
  hrowWidth : rowWidth.length=Q*ringWidth.length

namespace Parameters
variable {r Q d : ℕ}
noncomputable def ops (p : Parameters r Q d) :=
  RingProgram.modelRing p.t p.ht p.hd p.model p.modulus p.cache

def saved (p : Parameters r Q d) : Numerator.Saved :=
  LayoutProgramScalar.FromCounts.unsignedSaved p.hwords p.width p.power p.R p.aWord

def start (p : Parameters r Q d) : Fin Q := ⟨0,by have := p.hQ; omega⟩

def nodeCache (p : Parameters r Q d) := SourceCache.native (Q:=Q) p.t p.model p.modulus p.cache p.minusOne

def inverse (p : Parameters r Q d) : Fin Q → ModelCode p.t d := p.nodeCache.inverse

def negative (p : Parameters r Q d) (i : Fin Q) : ModelCode p.t d :=
  InterpolationCacheProgram.negativeValue p.t p.model p.modulus p.cache p.minusOne (p.nodeCache.node i)

def difference (p : Parameters r Q d) : Fin Q → Fin Q → ModelCode p.t d := p.nodeCache.difference

noncomputable def rows (p : Parameters r Q d) (u y : UniversalType r Q 1) :=
  LayoutScaledMatrices.sourceRow (LayoutNumerator.family r Q 1 p.aWord.length p.R)
    p.denom u 0 p.R (p.model.nodeUnits p.t Q p.ht p.hfield) y
end Parameters

variable {r Q d : ℕ}

structure Ready (p : Parameters r Q d) (a : Data) : Prop where
  work : WorkReady a
  input : ∀ u y : UniversalType r Q 1, InputFields a p.saved p.start u y
  ring : CachedReady p.t p.model p.modulus p.cache p.ops.zeroRun.1 p.ops.oneRun.1 p.minusOne (lowStore a)
  inverseDenominator : a.stacks 252=RingProgram.flat p.invDenom
  nodes : (a.stacks 22).length=Q
  limit : (a.stacks 47).length=p.R
  inverses : a.stacks 308=(List.ofFn (fun i=>RingProgram.flat (p.inverse i))).flatten
  negatives : a.stacks 309=(List.ofFn (fun i=>RingProgram.flat (p.negative i))).flatten
  differences : a.stacks 310=(List.ofFn (fun i=>(List.ofFn (fun j=>RingProgram.flat (p.difference i j))).flatten)).flatten
  ringWidth : a.stacks 311=p.ringWidth
  rowWidth : a.stacks 312=p.rowWidth
  zero : a.stacks 313=RingProgram.flat p.ops.zeroRun.1
  one : a.stacks 314=RingProgram.flat p.ops.oneRun.1

theorem Ready.frame {p : Parameters r Q d} {a b : Data} (h : Ready p a)
    (hb : b.stacks=a.stacks) : Ready p b := by
  constructor
  · exact h.work.frame hb
  · intro u y; exact inputFields_store_frame a b p.saved p.start u y (h.input u y) hb
  · exact cachedReady_store_frame p.t p.model p.modulus p.cache _ _ _ a b h.ring hb
  · simpa only [hb] using h.inverseDenominator
  · simpa only [hb] using h.nodes
  · simpa only [hb] using h.limit
  · simpa only [hb] using h.inverses
  · simpa only [hb] using h.negatives
  · simpa only [hb] using h.differences
  · simpa only [hb] using h.ringWidth
  · simpa only [hb] using h.rowWidth
  · simpa only [hb] using h.zero
  · simpa only [hb] using h.one

theorem Ready.metadata {p : Parameters r Q d} {a b : Data} (h : Ready p a)
    (mr mc : GlobalBasisMetadata.Metadata) (hb : b.stacks=metadataStacks a mr mc) : Ready p b := by
  have hf (j : Fin 320) (hj : j.val < 288 ∨ 293 < j.val) : b.stacks j=a.stacks j := by
    rw [hb,metadata_frame a mr mc j hj]
  constructor
  · exact h.work.metadata mr mc hb
  · intro u y
    apply inputFields_frame a b p.saved p.start u y (h.input u y)
    have hh := lowStore_metadata a mr mc b.regs
    simpa only [lowStore,projectState,hb] using hh
  · have hh := cachedReady_metadata p.t p.model p.modulus p.cache _ _ _ a mr mc b.regs h.ring
    simpa only [lowStore,projectState,hb] using hh
  · exact (hf 252 (Or.inl (by decide))).trans h.inverseDenominator
  · rw [hf 22 (Or.inl (by decide))]; exact h.nodes
  · rw [hf 47 (Or.inl (by decide))]; exact h.limit
  · exact (hf 308 (Or.inr (by decide))).trans h.inverses
  · exact (hf 309 (Or.inr (by decide))).trans h.negatives
  · exact (hf 310 (Or.inr (by decide))).trans h.differences
  · exact (hf 311 (Or.inr (by decide))).trans h.ringWidth
  · exact (hf 312 (Or.inr (by decide))).trans h.rowWidth
  · exact (hf 313 (Or.inr (by decide))).trans h.zero
  · exact (hf 314 (Or.inr (by decide))).trans h.one

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
