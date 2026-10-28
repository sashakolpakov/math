import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyFoldRel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramUniformBounds

namespace OAI.Algorithms

/-! Execution-associated sparse payloads. No uniqueness of raw encodings is
assumed: each assignment occurrence may supply a new related payload. -/
namespace SubexponentialSAT.SqrtLog.MomentsAssembly.Relational
open SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing MomentsProgram

theorem FoldRel.mono {A W : Type*} {step step' : A → W → A → Prop}
    (hstep : ∀ a w b, step a w b → step' a w b) {ws : List W} {a b : A}
    (h : FoldRel step ws a b) : FoldRel step' ws a b := by
  induction h with
  | nil a => exact .nil a
  | cons hx hxs ih => exact .cons (hstep _ _ _ hx) ih

section Model
variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
  (cache : RingProgram.ScalarCache p t) {n d : ℕ}
  (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
  (u J : ℕ)
  (relation : AssignmentContext → List Bool → Contribution n (baseWidth p t) d → Prop)

abbrev Raw := List (Product.Entry n (baseWidth p t) d)

def AssignmentStep (c : AssignmentContext) (seed : Raw p t (n:=n) (d:=d)) (x : List Bool)
    (out : Raw p t (n:=n) (d:=d)) : Prop :=
  ∃ value, relation c x value ∧
    out = weightedValue p t M cache table value.1 value.2 seed

def HeadRel (c : AssignmentContext) :=
  FoldRel (AssignmentStep p t M cache table relation c)

def HeadStep (support bucket : List Bool) (left : Raw p t (n:=n) (d:=d)) (h : HeadInput)
    (out : Raw p t (n:=n) (d:=d)) : Prop :=
  ∃ sum, HeadRel p t M cache table relation
    ⟨support,h.mask,h.context,bucket⟩ h.assignments [] sum ∧
    out = Product.run p t M cache table u J left sum []

def HeadsRel (support bucket : List Bool) :=
  FoldRel (HeadStep p t M cache table u J relation support bucket)

def SupportStep (bucket : List Bool) (hs : List HeadInput) (one seed : Raw p t (n:=n) (d:=d))
    (s : Finset (Fin n)) (out : Raw p t (n:=n) (d:=d)) : Prop :=
  ∃ product, HeadsRel p t M cache table u J relation (Squarefree.encodeMask s) bucket hs one product ∧
    out = supportValue p t M cache s product seed

def SupportsRel (bucket : List Bool) (hs : List HeadInput) (one : Raw p t (n:=n) (d:=d)) :=
  FoldRel (SupportStep p t M cache table u J relation bucket hs one)

def BucketStep (ss : List (Finset (Fin n))) (one seed : Raw p t (n:=n) (d:=d))
    (b : BucketInput) (out : Raw p t (n:=n) (d:=d)) : Prop :=
  SupportsRel p t M cache table u J relation b.context b.heads one ss seed out

def BucketsRel (ss : List (Finset (Fin n))) (one : Raw p t (n:=n) (d:=d)) :=
  FoldRel (BucketStep p t M cache table u J relation ss one)

theorem BucketsRel.mono {relation' : AssignmentContext → List Bool →
    Contribution n (baseWidth p t) d → Prop}
    (hrel : ∀ c x v, relation c x v → relation' c x v)
    {ss : List (Finset (Fin n))} {one : Raw p t (n:=n) (d:=d)}
    {bs : List BucketInput} {seed out : Raw p t (n:=n) (d:=d)}
    (h : BucketsRel p t M cache table u J relation ss one bs seed out) :
    BucketsRel p t M cache table u J relation' ss one bs seed out := by
  unfold BucketsRel at h ⊢
  apply FoldRel.mono (h := h)
  intro seed₁ bucket out₁ hb
  unfold BucketStep SupportsRel at hb ⊢
  apply FoldRel.mono (h := hb)
  intro seed₂ support out₂ hs
  unfold SupportStep at hs ⊢
  obtain ⟨product,hheads,rfl⟩ := hs
  refine ⟨product,?_,rfl⟩
  unfold HeadsRel at hheads ⊢
  apply FoldRel.mono (h := hheads)
  intro left head out₃ hh
  unfold HeadStep at hh ⊢
  obtain ⟨sum,hhead,rfl⟩ := hh
  refine ⟨sum,?_,rfl⟩
  unfold HeadRel at hhead ⊢
  apply FoldRel.mono (h := hhead)
  intro seed₃ x out₄ ha
  unfold AssignmentStep at ha ⊢
  obtain ⟨value,hvalue,rfl⟩ := ha
  exact ⟨value,hrel _ _ _ hvalue,rfl⟩

/-- The only abstract operation is a paid native assignment worker. Its actual
payload is existential and its size is controlled by validity and unique keys. -/
def AssignmentContract (produce : Code) (degree width : List Bool)
    (vars : Finset (Fin n)) (validFrame : (Fin 768 → List Bool) → Prop) (A : ℕ) : Prop :=
  ∀ c x (left seed : Raw p t (n:=n) (d:=d)) (high : Fin 768 → List Bool) (regs : Fin 40 → Bool),
    EntryInvariant vars u J left → EntryInvariant vars u J seed →
    validFrame high → c.Matches high → high 174 = x →
    let e := Product.environment p t M cache table degree width u J
    ∃ value, relation c x value ∧ EntryInvariant vars u J value.2 ∧
      ∃ k ≤ A, ∃ rr,
        Eval produce k (machine regs (Product.working e left [] seed) high)
          (machine rr (weightedStore e (Product.bytes left) (Product.bytes seed)
            (Product.bytes value.2) (RingProgram.flat value.1)) (Function.update high 174 []))
end Model
end SubexponentialSAT.SqrtLog.MomentsAssembly.Relational

end OAI.Algorithms
