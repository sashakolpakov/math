import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblySemanticsBounds

namespace OAI.Algorithms

/-! Uniform physical costs on valid, normalized sparse dictionaries.  The
invariant bounds actual serialized intermediate states, not arbitrary tapes.
Assignment production remains a charged native callback. -/
namespace SubexponentialSAT.SqrtLog.MomentsAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

abbrev EntryInvariant {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (entries : List (Product.Entry n B d)) : Prop :=
  ValidEntries vars u J entries ∧ (Sparse.keys entries).Nodup

def dictionaryCapacity {n : ℕ} (vars : Finset (Fin n)) (u J : ℕ) : ℕ :=
  u*J*(Sparse.supportUniverse vars J).card

def dictionaryByteEnvelope (B d W L : ℕ) : ℕ := L*(2*W+2*(d*B)+2)

theorem entryInvariant_empty {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ) :
    EntryInvariant vars u J ([] : List (Product.Entry n B d)) := by
  simp [EntryInvariant,ValidEntries,Sparse.keys]

theorem entryInvariant_keyBound {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (entries : List (Product.Entry n B d)) (h : EntryInvariant vars u J entries) :
    Normalize.KeyBound Squarefree.encodeIndex (n+u+J) entries := by
  intro a ha
  have hk := Squarefree.encodeIndex_length_le a.1 (h.1 a ha).1
  omega

theorem entryInvariant_sizes {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (entries : List (Product.Entry n B d)) (h : EntryInvariant vars u J entries) :
    entries.length ≤ dictionaryCapacity vars u J ∧
    (Product.bytes entries).length ≤
      dictionaryByteEnvelope B d (n+u+J) (dictionaryCapacity vars u J) := by
  exact valid_sizeBounds vars u J entries h.1 h.2

theorem rawProject_record_length_le {V R : Type*} [DecidableEq V]
    (s : Finset V) (entries : List (Squarefree.Index V × R)) :
    (Moments.rawProject s entries).length ≤ entries.length := by
  induction entries with
  | nil => simp [Moments.rawProject]
  | cons a entries ih =>
      by_cases h : a.1.vars = s <;> simp [Moments.rawProject,h] <;> omega

section Arithmetic
variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
  (cache : RingProgram.ScalarCache p t) {n d : ℕ}
  (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
  (vars : Finset (Fin n)) (u J : ℕ)

theorem entryInvariant_weighted
    (weight : RingProgram.Code (Word (baseWidth p t)) d)
    (jet seed : List (Product.Entry n (baseWidth p t) d))
    (hj : EntryInvariant vars u J jet) (hs : EntryInvariant vars u J seed) :
    EntryInvariant vars u J (weightedValue p t M cache table weight jet seed) :=
  ⟨weightedValue_valid p t M cache table vars u J weight jet seed hj.1 hs.1,
    weightedValue_nodup p t M cache table weight jet seed hs.2⟩

def normalizationEnvelope (B d W L : ℕ) : ℕ :=
  L*(220*(2*L+1)*(W+d*B+1)+MomentsProgram.Dictionary.codeBranchBudget B d+2)+1

def productEnvelope (B d n u J L : ℕ) : ℕ :=
  L*(Product.stepEnvelope B d n u J (L*L) L+2)+1

theorem productWork_le
    (left right : List (Product.Entry n (baseWidth p t) d))
    (hl : EntryInvariant vars u J left) (hr : EntryInvariant vars u J right) :
    Product.work p t M cache table u J left right [] ≤
      productEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) := by
  let L := dictionaryCapacity vars u J
  have hll := (entryInvariant_sizes vars u J left hl).1
  have hrl := (entryInvariant_sizes vars u J right hr).1
  have hh := Product.work_le p t M cache table u J (L*L) left right []
    (fun a ha => (hl.1 a ha).1) (fun a ha => (hr.1 a ha).1)
    (by intro a ha; simp at ha) (by simpa using Nat.mul_le_mul hll hrl)
  have he : Product.stepEnvelope (baseWidth p t) d n u J (L*L) right.length ≤
      Product.stepEnvelope (baseWidth p t) d n u J (L*L) L := by
    dsimp [Product.stepEnvelope]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hrl) _
  exact hh.trans (Nat.add_le_add_right
    (Nat.mul_le_mul hll (Nat.add_le_add_right he 2)) 1)

omit [Fact (Nat.Prime p)] in
theorem rawProject_keyBound (s : Finset (Fin n))
    (product : List (Product.Entry n (baseWidth p t) d))
    (hp : EntryInvariant vars u J product) :
    Normalize.KeyBound Squarefree.encodeIndex (n+u+J) (Moments.rawProject s product) := by
  have hv := rawProject_validEntries vars u J s product hp.1
  intro a ha
  have hk := Squarefree.encodeIndex_length_le a.1 (hv a ha).1
  omega

theorem projectionNormalizeWork_le (s : Finset (Fin n))
    (product seed : List (Product.Entry n (baseWidth p t) d))
    (hp : EntryInvariant vars u J product) (hs : EntryInvariant vars u J seed) :
    Normalize.work p t M cache Squarefree.encodeIndex (Moments.rawProject s product) seed ≤
      normalizationEnvelope (baseWidth p t) d (n+u+J) (dictionaryCapacity vars u J) := by
  let L := dictionaryCapacity vars u J
  have hpl := (rawProject_record_length_le s product).trans
    (entryInvariant_sizes vars u J product hp).1
  have hsl := (entryInvariant_sizes vars u J seed hs).1
  have hh := Normalize.work_le p t M cache Squarefree.encodeIndex (n+u+J) (2*L)
    (Moments.rawProject s product) seed (rawProject_keyBound p t vars u J s product hp)
    (entryInvariant_keyBound vars u J seed hs) (by omega)
  exact hh.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hpl) 1)

def finishHeadEnvelope (B d n u J L H : ℕ) : ℕ :=
  14*dictionaryByteEnvelope B d (n+u+J) L+4*H+productEnvelope B d n u J L+23

theorem finishHeadBudget_le
    (left right : List (Product.Entry n (baseWidth p t) d))
    (high : Fin 768 → List Bool) (H : ℕ)
    (hl : EntryInvariant vars u J left) (hr : EntryInvariant vars u J right)
    (hc : (high 175).length ≤ H) (hm : (high 178).length ≤ H) :
    finishHeadBudget p t M cache table u J left right high ≤
      finishHeadEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H := by
  have hout : EntryInvariant vars u J (Product.run p t M cache table u J left right []) :=
    ⟨Product.run_valid p t M cache table vars u J left right [] hl.1 hr.1 (by simp),
      Product.run_nodup p t M cache table u J left right [] (by simp [Sparse.keys])⟩
  have hb := (entryInvariant_sizes vars u J right hr).2
  have ho := (entryInvariant_sizes vars u J _ hout).2
  have hw := productWork_le p t M cache table vars u J left right hl hr
  dsimp [finishHeadBudget,finishHeadEnvelope]
  omega

def finishSupportEnvelope (B d n u J L : ℕ) : ℕ :=
  let E := dictionaryByteEnvelope B d (n+u+J) L
  200*(E+1)*(n+2)+14*n+27*E+9*d+normalizationEnvelope B d (n+u+J) L+60

theorem finishSupportBudget_le (s : Finset (Fin n))
    (product seed : List (Product.Entry n (baseWidth p t) d))
    (hp : EntryInvariant vars u J product) (hs : EntryInvariant vars u J seed) :
    finishSupportBudget p t M cache s product seed ≤
      finishSupportEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) := by
  have hout : EntryInvariant vars u J (supportValue p t M cache s product seed) :=
    ⟨supportValue_valid p t M cache vars u J s product seed hp.1 hs.1,
      supportValue_nodup p t M cache s product seed hs.2⟩
  have hpj := rawProject_keyBound p t vars u J s product hp
  have hpl := (rawProject_record_length_le s product).trans
    (entryInvariant_sizes vars u J product hp).1
  have hpjbytes := (Product.bytes_length_le (Moments.rawProject s product) (n+u+J) hpj).trans
    (Nat.mul_le_mul_right _ hpl)
  have hb := (entryInvariant_sizes vars u J product hp).2
  have hsbytes := (entryInvariant_sizes vars u J seed hs).2
  have ho := (entryInvariant_sizes vars u J _ hout).2
  have hw := projectionNormalizeWork_le p t M cache vars u J s product seed hp hs
  have hbmul := Nat.mul_le_mul_right (n+2) (Nat.add_le_add_right hb 1)
  dsimp [finishSupportBudget,finishSupportEnvelope]
  change (Product.bytes (Moments.rawProject s product)).length ≤
    dictionaryByteEnvelope (baseWidth p t) d (n+u+J) (dictionaryCapacity vars u J) at hpjbytes
  nlinarith

variable (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)
  (cost : AssignmentContext → List Bool → List (Product.Entry n (baseWidth p t) d) →
    List (Product.Entry n (baseWidth p t) d) → ℕ)

def assignmentEnvelope (B d W L H A : ℕ) : ℕ :=
  9*H+A+weightedEnvelope B d W (2*L)+2*dictionaryByteEnvelope B d W L+10

theorem assignmentBudget_le (c : AssignmentContext) (x : List Bool)
    (left seed : List (Product.Entry n (baseWidth p t) d)) (H A : ℕ)
    (hx : x.length ≤ H) (hc : cost c x left seed ≤ A)
    (hj : EntryInvariant vars u J (meaning c x).2) (hs : EntryInvariant vars u J seed) :
    assignmentBudget p t M cache table meaning cost c x left seed ≤
      assignmentEnvelope (baseWidth p t) d (n+u+J) (dictionaryCapacity vars u J) H A := by
  have hjs := entryInvariant_sizes vars u J (meaning c x).2 hj
  have hss := entryInvariant_sizes vars u J seed hs
  have hw := weightedBudget_le p t M cache table (meaning c x).1 (meaning c x).2 seed
    (n+u+J) (2*dictionaryCapacity vars u J)
    (entryInvariant_keyBound vars u J _ hj) (entryInvariant_keyBound vars u J seed hs) (by omega)
  dsimp [assignmentBudget,assignmentEnvelope]
  omega

theorem headWork_le (c : AssignmentContext) (xs : List (List Bool))
    (left seed : List (Product.Entry n (baseWidth p t) d)) (H A : ℕ)
    (hx : ∀ x ∈ xs, x.length ≤ H)
    (hc : ∀ x ∈ xs, ∀ a, EntryInvariant vars u J a → cost c x left a ≤ A)
    (hm : ∀ x ∈ xs, EntryInvariant vars u J (meaning c x).2)
    (hs : EntryInvariant vars u J seed) :
    headWork p t M cache table meaning cost c left xs seed ≤
      xs.length*(assignmentEnvelope (baseWidth p t) d (n+u+J)
        (dictionaryCapacity vars u J) H A+2)+1 := by
  induction xs generalizing seed with
  | nil => simp [headWork]
  | cons x xs ih =>
    have hw := assignmentBudget_le p t M cache table vars u J meaning cost c x left seed H A
      (hx x (by simp)) (hc x (by simp) seed hs) (hm x (by simp)) hs
    have hn := entryInvariant_weighted p t M cache table vars u J (meaning c x).1
      (meaning c x).2 seed (hm x (by simp)) hs
    have ht := ih _ (fun y hy => hx y (by simp [hy]))
      (fun y hy => hc y (by simp [hy])) (fun y hy => hm y (by simp [hy])) hn
    simp only [headWork,List.length_cons]
    nlinarith

/-- Explicit bounds for every field physically parsed in a head record. -/
def HeadSize (H X : ℕ) (h : HeadInput) : Prop :=
  h.bits.length ≤ H ∧ h.mask.length ≤ H ∧ h.context.length ≤ H ∧
    (rawFrames h.assignments).length ≤ H ∧ h.assignments.length ≤ X ∧
    ∀ x ∈ h.assignments, x.length ≤ H

def headEnvelope (B d n u J L H X A : ℕ) : ℕ :=
  36*H+30+X*(assignmentEnvelope B d (n+u+J) L H A+2)+
    finishHeadEnvelope B d n u J L H

theorem headStepBudget_le (high : Fin 768 → List Bool) (h : HeadInput) (tail : List Bool)
    (left : List (Product.Entry n (baseWidth p t) d)) (H X A : ℕ)
    (hsize : HeadSize H X h) (hl : EntryInvariant vars u J left)
    (hm : ∀ x ∈ h.assignments, EntryInvariant vars u J (meaning (headContext high h) x).2)
    (hc : ∀ x ∈ h.assignments, ∀ a, EntryInvariant vars u J a →
      cost (headContext high h) x left a ≤ A) :
    headStepBudget p t M cache table u J meaning cost high h tail left ≤
      headEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X A := by
  have hh := headWork_le p t M cache table vars u J meaning cost (headContext high h)
    h.assignments left [] H A hsize.2.2.2.2.2 hc hm (entryInvariant_empty vars u J)
  have hr : EntryInvariant vars u J
      (headRun p t M cache table meaning (headContext high h) h.assignments []) :=
    ⟨headRun_valid p t M cache table vars u J meaning _ _ [] (fun x hx => (hm x hx).1) (by simp),
      headRun_nodup p t M cache table meaning _ _ [] (by simp [Sparse.keys])⟩
  have hf := finishHeadBudget_le p t M cache table vars u J left _
    (assignmentStream (headHigh high h tail) []) H hl hr
    (by simpa [assignmentStream,headHigh,headHigh3,headHigh2,headHigh1] using hsize.2.2.1)
    (by simpa [assignmentStream,headHigh,headHigh3,headHigh2,headHigh1] using hsize.2.1)
  have hcount := Nat.mul_le_mul_right
    (assignmentEnvelope (baseWidth p t) d (n+u+J) (dictionaryCapacity vars u J) H A+2)
    hsize.2.2.2.2.1
  rcases hsize with ⟨hbits,hmask,hcontext,hassignments,hcount',hx⟩
  dsimp [headStepBudget,headHeaderBudget,headEnvelope]
  omega

theorem headsWork_le (high : Fin 768 → List Bool) (hs : List HeadInput)
    (left : List (Product.Entry n (baseWidth p t) d)) (H X A : ℕ)
    (hsize : ∀ h ∈ hs, HeadSize H X h) (hl : EntryInvariant vars u J left)
    (hm : ∀ h ∈ hs, ∀ x ∈ h.assignments,
      EntryInvariant vars u J (meaning (headContext high h) x).2)
    (hc : ∀ h ∈ hs, ∀ x ∈ h.assignments, ∀ a b,
      EntryInvariant vars u J a → EntryInvariant vars u J b →
      cost (headContext high h) x a b ≤ A) :
    headsWork p t M cache table u J meaning cost high hs left ≤
      hs.length*(headEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X A+2)+1 := by
  induction hs generalizing left with
  | nil => simp [headsWork]
  | cons h hs ih =>
    have hh := headStepBudget_le p t M cache table vars u J meaning cost high h [] left H X A
      (hsize h (by simp)) hl (hm h (by simp))
      (fun x hx a ha => hc h (by simp) x hx left a hl ha)
    have hn : EntryInvariant vars u J (headStepValue p t M cache table u J meaning high h left) :=
      ⟨headStepValue_valid p t M cache table vars u J meaning high h left
        (fun x hx => (hm h (by simp) x hx).1) hl.1,
        headStepValue_nodup p t M cache table meaning u J high h left⟩
    have ht := ih _ (fun h hh => hsize h (by simp [hh])) hn
      (fun h hh => hm h (by simp [hh])) (fun h hh => hc h (by simp [hh]))
    simp only [headsWork,List.length_cons]
    nlinarith

def supportEnvelope (B d n u J L H X Y A : ℕ) : ℕ :=
  9*n+7*dictionaryByteEnvelope B d (n+u+J) L+7*H+19+
    Y*(headEnvelope B d n u J L H X A+2)+finishSupportEnvelope B d n u J L

theorem supportStepBudget_le (high : Fin 768 → List Bool) (hs : List HeadInput)
    (tail : List Bool) (one seed : List (Product.Entry n (baseWidth p t) d))
    (s : Finset (Fin n)) (H X Y A : ℕ)
    (hsize : ∀ h ∈ hs, HeadSize H X h) (hcount : hs.length ≤ Y)
    (hmaster : (high 170).length ≤ H)
    (ho : EntryInvariant vars u J one) (hi : EntryInvariant vars u J seed)
    (hm : ∀ h ∈ hs, ∀ x ∈ h.assignments, EntryInvariant vars u J
      (meaning (headContext (Function.update high 168 (Squarefree.encodeMask s)) h) x).2)
    (hc : ∀ h ∈ hs, ∀ x ∈ h.assignments, ∀ a b,
      EntryInvariant vars u J a → EntryInvariant vars u J b →
      cost (headContext (Function.update high 168 (Squarefree.encodeMask s)) h) x a b ≤ A) :
    supportStepBudget p t M cache table u J meaning cost high hs tail one seed s ≤
      supportEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X Y A := by
  have hh := headsWork_le p t M cache table vars u J meaning cost
    (supportHigh high (Squarefree.encodeMask s) tail) hs one H X A hsize ho
    (by simpa [headContext,supportHigh] using hm)
    (by simpa [headContext,supportHigh] using hc)
  have hp : EntryInvariant vars u J (supportProduct p t M cache table u J meaning high hs one s) :=
    ⟨supportProduct_valid p t M cache table vars u J meaning high hs one s
      (fun h hh x hx => (hm h hh x hx).1) ho.1,
      headsRun_nodup p t M cache table meaning u J _ hs one ho.2⟩
  have hf := finishSupportBudget_le p t M cache vars u J s _ seed hp hi
  have hb := (entryInvariant_sizes vars u J one ho).2
  have hcount' := Nat.mul_le_mul_right
    (headEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X A+2) hcount
  dsimp [supportStepBudget,supportEnvelope]
  omega

theorem supportsRun_entryInvariant (high : Fin 768 → List Bool) (hs : List HeadInput)
    (one seed : List (Product.Entry n (baseWidth p t) d)) (ss : List (Finset (Fin n)))
    (ho : EntryInvariant vars u J one) (hi : EntryInvariant vars u J seed)
    (hm : ∀ s ∈ ss, ∀ h ∈ hs, ∀ x ∈ h.assignments, EntryInvariant vars u J
      (meaning (headContext (Function.update high 168 (Squarefree.encodeMask s)) h) x).2) :
    EntryInvariant vars u J (supportsRun p t M cache table u J meaning high hs one ss seed) := by
  induction ss generalizing seed with
  | nil => exact hi
  | cons s ss ih =>
    have hp := supportProduct_valid p t M cache table vars u J meaning high hs one s
      (fun h hh x hx => (hm s (by simp) h hh x hx).1) ho.1
    apply ih _ _ (fun q hq => hm q (by simp [hq]))
    exact ⟨supportValue_valid p t M cache vars u J s _ seed hp hi.1,
      supportValue_nodup p t M cache s _ seed hi.2⟩

theorem supportsWork_le (high : Fin 768 → List Bool) (hs : List HeadInput)
    (one seed : List (Product.Entry n (baseWidth p t) d)) (ss : List (Finset (Fin n)))
    (H X Y A : ℕ)
    (hsize : ∀ h ∈ hs, HeadSize H X h) (hcount : hs.length ≤ Y)
    (hmaster : (high 170).length ≤ H)
    (ho : EntryInvariant vars u J one) (hi : EntryInvariant vars u J seed)
    (hm : ∀ s ∈ ss, ∀ h ∈ hs, ∀ x ∈ h.assignments, EntryInvariant vars u J
      (meaning (headContext (Function.update high 168 (Squarefree.encodeMask s)) h) x).2)
    (hc : ∀ s ∈ ss, ∀ h ∈ hs, ∀ x ∈ h.assignments, ∀ a b,
      EntryInvariant vars u J a → EntryInvariant vars u J b →
      cost (headContext (Function.update high 168 (Squarefree.encodeMask s)) h) x a b ≤ A) :
    supportsWork p t M cache table u J meaning cost high hs one ss seed ≤
      ss.length*(supportEnvelope (baseWidth p t) d n u J
        (dictionaryCapacity vars u J) H X Y A+2)+2 := by
  have hh := scanWork_bound_on
    (fun a s => supportStepBudget p t M cache table u J meaning cost high hs [] one a s)
    (fun a s => supportValue p t M cache s (supportProduct p t M cache table u J meaning high hs one s) a)
    (EntryInvariant vars u J) ss
    (supportEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X Y A)
    (by
      intro a ha s hss
      have hp := supportProduct_valid p t M cache table vars u J meaning high hs one s
        (fun h hh x hx => (hm s hss h hh x hx).1) ho.1
      exact ⟨supportValue_valid p t M cache vars u J s _ a hp ha.1,
        supportValue_nodup p t M cache s _ a ha.2⟩)
    (by
      intro a ha s hss
      exact supportStepBudget_le p t M cache table vars u J meaning cost high hs [] one a s H X Y A
        hsize hcount hmaster ho ha (hm s hss) (hc s hss)) seed hi
  unfold supportsWork
  omega

/-- Includes all fields that the bucket header and cleanup physically scan. -/
def BucketSize (H X Y : ℕ) (b : BucketInput) : Prop :=
  b.bits.length ≤ H ∧ b.context.length ≤ H ∧ (rawFrames (b.heads.map HeadInput.bits)).length ≤ H ∧
    b.heads.length ≤ Y ∧ ∀ h ∈ b.heads, HeadSize H X h

theorem rawFrames_member_length_le (xs : List (List Bool)) (x : List Bool) (hx : x ∈ xs) :
    x.length ≤ (rawFrames xs).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl|hx
    · simp only [rawFrames,List.length_append,Encoding.length_frame]; omega
    · have hh := ih hx
      simp only [rawFrames,List.length_append,Encoding.length_frame]
      omega

theorem headSize_of_bits (h : HeadInput) (H X : ℕ)
    (hh : h.bits.length ≤ H) (hx : h.assignments.length ≤ X) : HeadSize H X h := by
  have hb : 2*h.mask.length+1+(2*h.context.length+1)+
      (2*(rawFrames h.assignments).length+1) ≤ H := by
    simpa [HeadInput.bits,Nat.add_assoc] using hh
  refine ⟨hh,by omega,by omega,by omega,hx,?_⟩
  intro x hx
  have hraw := rawFrames_member_length_le h.assignments x hx
  omega

theorem bucketSize_of_bits (b : BucketInput) (H X Y : ℕ)
    (hb : b.bits.length ≤ H) (hy : b.heads.length ≤ Y)
    (hx : ∀ h ∈ b.heads, h.assignments.length ≤ X) : BucketSize H X Y b := by
  have hbits : 2*b.context.length+1+
      (2*(rawFrames (b.heads.map HeadInput.bits)).length+1) ≤ H := by
    simpa [BucketInput.bits] using hb
  refine ⟨hb,by omega,by omega,hy,?_⟩
  intro h hh
  apply headSize_of_bits h H X _ (hx h hh)
  have hraw := rawFrames_member_length_le (b.heads.map HeadInput.bits) h.bits
    (List.mem_map.mpr ⟨h,hh,rfl⟩)
  omega

def bucketEnvelope (B d n u J L H X Y S A : ℕ) : ℕ :=
  38*H+34+S*(supportEnvelope B d n u J L H X Y A+2)

theorem bucketStepBudget_le (high : Fin 768 → List Bool) (b : BucketInput) (tail : List Bool)
    (one seed : List (Product.Entry n (baseWidth p t) d)) (ss : List (Finset (Fin n)))
    (H X Y S A : ℕ)
    (hsize : BucketSize H X Y b) (hcount : ss.length ≤ S)
    (hmaster : (high 169).length ≤ H)
    (ho : EntryInvariant vars u J one) (hi : EntryInvariant vars u J seed)
    (hm : ∀ s ∈ ss, ∀ h ∈ b.heads, ∀ x ∈ h.assignments, EntryInvariant vars u J
      (meaning (headContext (Function.update (Function.update high 177 b.context)
        168 (Squarefree.encodeMask s)) h) x).2)
    (hc : ∀ s ∈ ss, ∀ h ∈ b.heads, ∀ x ∈ h.assignments, ∀ a c,
      EntryInvariant vars u J a → EntryInvariant vars u J c →
      cost (headContext (Function.update (Function.update high 177 b.context)
        168 (Squarefree.encodeMask s)) h) x a c ≤ A) :
    bucketStepBudget p t M cache table u J meaning cost high ss one seed b tail ≤
      bucketEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X Y S A := by
  have hw := supportsWork_le p t M cache table vars u J meaning cost (bucketHigh high b tail)
    b.heads one seed ss H X Y A hsize.2.2.2.2 hsize.2.2.2.1
    (by simpa [bucketHigh,bucketHigh3,bucketHigh2,bucketHigh1] using hsize.2.2.1) ho hi
    (by simpa [headContext,bucketHigh,bucketHigh3,bucketHigh2,bucketHigh1] using hm)
    (by simpa [headContext,bucketHigh,bucketHigh3,bucketHigh2,bucketHigh1] using hc)
  have hcount' := Nat.mul_le_mul_right
    (supportEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X Y A+2) hcount
  rcases hsize with ⟨hbits,hcontext,hheads,hheadsCount,hheadsSize⟩
  dsimp [bucketStepBudget,bucketHeaderBudget,bucketEnvelope]
  omega

/-- A uniform polynomial in the actual dictionary, field-size, loop-count,
and paid producer bounds.  Bucket count enters once, outside the support,
head, and assignment loops. -/
theorem bucketsWork_le (high : Fin 768 → List Bool)
    (one seed : List (Product.Entry n (baseWidth p t) d)) (ss : List (Finset (Fin n)))
    (bs : List BucketInput) (H X Y S A : ℕ)
    (hsize : ∀ b ∈ bs, BucketSize H X Y b) (hcount : ss.length ≤ S)
    (hmaster : (high 169).length ≤ H)
    (ho : EntryInvariant vars u J one) (hi : EntryInvariant vars u J seed)
    (hm : ∀ b ∈ bs, ∀ s ∈ ss, ∀ h ∈ b.heads, ∀ x ∈ h.assignments, EntryInvariant vars u J
      (meaning (headContext (Function.update (Function.update high 177 b.context)
        168 (Squarefree.encodeMask s)) h) x).2)
    (hc : ∀ b ∈ bs, ∀ s ∈ ss, ∀ h ∈ b.heads, ∀ x ∈ h.assignments, ∀ a c,
      EntryInvariant vars u J a → EntryInvariant vars u J c →
      cost (headContext (Function.update (Function.update high 177 b.context)
        168 (Squarefree.encodeMask s)) h) x a c ≤ A) :
    bucketsWork p t M cache table u J meaning cost high ss one bs seed ≤
      bs.length*(bucketEnvelope (baseWidth p t) d n u J
        (dictionaryCapacity vars u J) H X Y S A+2)+2 := by
  have hh := scanWork_bound_on
    (fun a (b : {b // b ∈ bs}) => bucketStepBudget p t M cache table u J meaning cost high ss one a b.val [])
    (fun a (b : {b // b ∈ bs}) => bucketStepValue p t M cache table u J meaning high ss one a b.val)
    (EntryInvariant vars u J) bs.attach
    (bucketEnvelope (baseWidth p t) d n u J (dictionaryCapacity vars u J) H X Y S A)
    (by
      intro a ha b hb
      exact supportsRun_entryInvariant p t M cache table vars u J meaning
        (Function.update high 177 b.val.context) b.val.heads one a ss ho ha (hm b.val b.property))
    (by
      intro a ha b hb
      exact bucketStepBudget_le p t M cache table vars u J meaning cost high b.val [] one a ss
        H X Y S A (hsize b.val b.property) hcount hmaster ho ha
        (hm b.val b.property) (hc b.val b.property)) seed hi
  simp only [List.length_attach] at hh
  unfold bucketsWork
  omega

end Arithmetic
end SubexponentialSAT.SqrtLog.MomentsAssembly

end OAI.Algorithms
