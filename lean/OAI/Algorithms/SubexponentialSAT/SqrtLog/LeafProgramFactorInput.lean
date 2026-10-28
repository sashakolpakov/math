import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorExpanded
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorIncidence
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorPayload

namespace OAI.Algorithms

/-! Physical factor inputs that are retained by the incidence producer. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram

noncomputable def sourceContext {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (n u J : ℕ) (width : List Bool) (hw : width.length=baseWidth 3 p.t) : Context 3 p.t n d :=
  ⟨p.modulus,p.cache,p.hz,HornerProgram.modelTable p.t p.model p.modulus p.cache,u,J,width,hw⟩

structure HashInput {t n d : ℕ} (ctx : Context 3 t n d)
    (minus : RingProgram.Code (Word (baseWidth 3 t)) d)
    (one seed : Raw (p:=3) (t:=t) (n:=n) (d:=d))
    (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (HashInputProgram.Expansion.encodedClauses source).length × ZMod 3))
    (digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode 3 t)))
    (b : ℕ) (a : Data) : Prop where
  raw : a.stacks 154=(HashInputProgram.Loop.rawInput b terms).reverse
  formula : a.stacks 700=ExecQuantitativeSparsify.encodeRawFormula source
  width : (a.stacks 708).length=b
  modulus : BinaryArithmetic.toNat (a.stacks 707)=(HashInputProgram.Expansion.encodedClauses source).length
  ringShape : (a.stacks 280).length=d*baseWidth 3 t
  output : a.stacks 64=[]
  expand : ∀ i ∈ Expansion.scratch,a.stacks i=[]
  work358 : a.stacks 358=[]
  work359 : a.stacks 359=[]
  low : ∀ i,a.stacks (indicatorStacks (Memory.lowPort i))=IdempotentApplyProgram.Steps.low ctx i
  one : a.stacks 69=Product.bytes one
  minus : a.stacks 76=RingProgram.flat minus
  tape : a.stacks 143=IdempotentApplyProgram.triplesTape digits
  shape : (a.stacks 88).length=n
  work : ∀ i ∈ FactorServices.indicatorScratch,a.stacks (indicatorStacks i)=[]
  seed : a.stacks 151=Product.bytes seed
  temporary : a.stacks 159=[]

theorem HashInput.frame {t n d : ℕ} {ctx : Context 3 t n d}
    {minus : RingProgram.Code (Word (baseWidth 3 t)) d}
    {one seed : Raw (p:=3) (t:=t) (n:=n) (d:=d)}
    {source : List (List (SAT.Literal (Fin n)))}
    {terms : List (Fin (HashInputProgram.Expansion.encodedClauses source).length × ZMod 3)}
    {digits : List (IdempotentApplyProgram.Triple (RingProgram.ScalarCode 3 t))}
    {b : ℕ} {a z : Data} (h : HashInput ctx minus one seed source terms digits b a)
    (hz : ∀ i : Fin 768,i≠62 → z.stacks i=a.stacks i) :
    HashInput ctx minus one seed source terms digits b z := by
  constructor
  · rw [hz 154 (by decide)]; exact h.raw
  · rw [hz 700 (by decide)]; exact h.formula
  · rw [hz 708 (by decide)]; exact h.width
  · rw [hz 707 (by decide)]; exact h.modulus
  · rw [hz 280 (by decide)]; exact h.ringShape
  · rw [hz 64 (by decide)]; exact h.output
  · intro i hi
    have hne : i≠(62 : Fin 768) := by
      intro he
      subst i
      simp [Expansion.scratch] at hi
    rw [hz i hne]
    exact h.expand i hi
  · rw [hz 358 (by decide)]; exact h.work358
  · rw [hz 359 (by decide)]; exact h.work359
  · intro i
    rw [hz _ (by rw [indicatorStacks_low]; exact low_ne i 62 (by decide))]
    exact h.low i
  · rw [hz 69 (by decide)]; exact h.one
  · rw [hz 76 (by decide)]; exact h.minus
  · rw [hz 143 (by decide)]; exact h.tape
  · rw [hz 88 (by decide)]; exact h.shape
  · intro i hi
    have hne : indicatorStacks i≠62 := by
      intro he
      have hi62 : i=(62 : Fin 96) :=
        indicatorStacks_injective (he.trans (by rfl))
      subst i
      simp [FactorServices.indicatorScratch] at hi
    rw [hz _ hne]
    exact h.work i hi
  · rw [hz 151 (by decide)]; exact h.seed
  · rw [hz 159 (by decide)]; exact h.temporary

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
