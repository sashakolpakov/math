import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramConcreteEncode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramConcreteTuples
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramSemantics

namespace OAI.Algorithms

/-! Certificates below are constructed from ProducedHead, not supplied as
cardinality or oracle assumptions. They name the actual free-head fibers. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete
open BucketProgram MomentsAssembly
open scoped BigOperators

structure HeadSemantics {n r : ℕ} (H : Finset (Fin n))
    (head : {v : Fin n // v∉H} → Fin r) (g : Fin r)
    (D : ℕ) (C : ℕ → ℕ → ℤ) (table : HeadTable) where
  label : (Moments.Head head g → Bool) → List Bool
  encode : (Moments.Head head g → Bool) → List Bool
  input : {key : List Bool // key∈Finset.univ.image label} → HeadInput
  encode_eq : ∀ a,encode a=ambientEncode H head g a
  kernel : ∀ x y,label x=label y ↔ ∀ j : Fin D,
    (∑ v : Moments.Head head g,C j.val v.val.val.val*(if x v then 1 else 0))=
    (∑ v : Moments.Head head g,C j.val v.val.val.val*(if y v then 1 else 0))
  input_injective : Function.Injective input
  input_mask : ∀ y,(input y).mask=table.mask
  input_context : ∀ y,(input y).context=table.context
  choices_nodup : table.choices.Nodup
  choices_mem : ∀ h,h∈table.choices ↔ ∃ y,input y=h
  fiber_enum : ∀ y,∃ xs : List {a : Moments.Head head g → Bool // label a=y.val},
    xs.Nodup ∧ (∀ a,a∈xs) ∧ xs.map (fun a=>encode a.val)=(input y).assignments

def semanticHead {n r D : ℕ} (H : Finset (Fin n))
    (head : {v : Fin n // v∉H} → Fin r) (g : Fin r)
    (js : List ℕ) (hb : ∀ v∈js,v < n) (hn : js.Nodup)
    (hs : ∀ v : Fin n,v.val∈js ↔ ∃ hv : v∉H,head ⟨v,hv⟩=g)
    (W : List Bool) (ys : List (List (List Bool))) (C : ℕ → ℕ → ℤ)
    (hk : KeyKernel C D js W ys) (mask context : List Bool) :
    HeadSemantics H head g D C
      (RecordModel.modelTable (records:=Controller.labelledRecords W ys js n js.length) mask context) where
  label := (freeModel H head g js hb hn hs W ys).label
  encode := (freeModel H head g js hb hn hs W ys).encode
  input := (freeModel H head g js hb hn hs W ys).inputHead mask context
  encode_eq := freeModel_encode H head g js hb hn hs W ys
  kernel := freeModel_key_iff H head g js hb hn hs W ys C hk
  input_injective := (freeModel H head g js hb hn hs W ys).inputHead_injective mask context
  input_mask := by intro y; rfl
  input_context := by intro y; rfl
  choices_nodup := (freeModel H head g js hb hn hs W ys).model_choices_nodup mask context
  choices_mem := (freeModel H head g js hb hn hs W ys).model_choices_mem mask context
  fiber_enum := (freeModel H head g js hb hn hs W ys).fiber_enumeration mask context

theorem producedHead_semantics {n r N D B z : ℕ} {base : LeafHeadSetupProgram.Data}
    {rows : List (List Bool)} {low : List Bool}
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {table : HeadTable}
    (H : Finset (Fin n)) (head : {v : Fin n // v∉H} → Fin r) (g : Fin r)
    (hp : LeafHeadSetupProgram.ProducedHead base n N D rows low Rel B z table)
    (hs : ∀ v : Fin n,v.val∈LeafHeadSetupProgram.selectedHeads n rows low z ↔
      ∃ hv : v∉H,head ⟨v,hv⟩=g)
    (C : ℕ → ℕ → ℤ)
    (hrel : ∀ j v p,j < D→v < n→Rel j v p→
      SubexponentialSAT.BinaryArithmetic.toNat p.2 ≤ SubexponentialSAT.BinaryArithmetic.toNat (base.stacks 141) ∧
      (SubexponentialSAT.BinaryArithmetic.toNat p.1 : ℤ)-(SubexponentialSAT.BinaryArithmetic.toNat p.2 : ℤ)=C j v) :
    Nonempty (HeadSemantics H head g D C table) := by
  have hb : ∀ v∈LeafHeadSetupProgram.selectedHeads n rows low z,v < n :=
    HeadIdentifierProgram.chosenIds_bound _ _
  have hn : (LeafHeadSetupProgram.selectedHeads n rows low z).Nodup :=
    HeadIdentifierProgram.chosenIds_nodup _ _
  obtain ⟨ys,ht,hk⟩ := producedHead_kernel hp C (fun j v p hj hv hr=>hrel j v p hj (hb v hv) hr)
  rw [ht]
  exact ⟨semanticHead H head g _ hb hn hs _ ys C hk _ _⟩

theorem producedHeads_get {n N D B z : ℕ} {base : LeafHeadSetupProgram.Data}
    {rows : List (List Bool)} {low : List Bool}
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {tables : List HeadTable}
    (hp : LeafHeadSetupProgram.ProducedHeads base n N D rows low Rel B z tables)
    (i : Fin tables.length) :
    LeafHeadSetupProgram.ProducedHead base n N D rows low Rel B (z+i.val) (tables.get i) := by
  induction hp with
  | nil => exact Fin.elim0 i
  | @cons z h hs hh ht ih =>
      refine Fin.cases ?_ (fun j=>?_) i
      · simpa using hh
      · simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih j

theorem producedHeads_semantics {n r N D B z : ℕ} {base : LeafHeadSetupProgram.Data}
    {rows : List (List Bool)} {low : List Bool}
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {tables : List HeadTable}
    (H : Finset (Fin n)) (head : {v : Fin n // v∉H} → Fin r)
    (hp : LeafHeadSetupProgram.ProducedHeads base n N D rows low Rel B z tables)
    (hlen : tables.length=r)
    (hs : ∀ g : Fin r,∀ v : Fin n,v.val∈LeafHeadSetupProgram.selectedHeads n rows low (z+g.val) ↔
      ∃ hv : v∉H,head ⟨v,hv⟩=g)
    (C : ℕ → ℕ → ℤ)
    (hrel : ∀ j v p,j < D→v < n→Rel j v p→
      SubexponentialSAT.BinaryArithmetic.toNat p.2 ≤ SubexponentialSAT.BinaryArithmetic.toNat (base.stacks 141) ∧
      (SubexponentialSAT.BinaryArithmetic.toNat p.1 : ℤ)-(SubexponentialSAT.BinaryArithmetic.toNat p.2 : ℤ)=C j v) :
    Nonempty (∀ g : Fin r,HeadSemantics H head g D C (tables.get (Fin.cast hlen.symm g))) := by
  subst r
  exact ⟨fun g=>(producedHead_semantics H head g (producedHeads_get hp g) (hs g) C hrel).some⟩

def familyInput {n r D : ℕ} {H : Finset (Fin n)}
    {head : {v : Fin n // v∉H} → Fin r} {C : ℕ → ℕ → ℤ} {tables : Fin r → HeadTable}
    (s : ∀ g,HeadSemantics H head g D C (tables g))
    (y : ∀ g,Moments.LabelValue (fun g=>(s g).label) g) : BucketInput :=
  Representative.bucket n (tupleHeads (fun g=>(s g).input) y)

theorem family_enumeration {n r D : ℕ} {H : Finset (Fin n)}
    {head : {v : Fin n // v∉H} → Fin r} {C : ℕ → ℕ → ℤ} {tables : Fin r → HeadTable}
    (s : ∀ g,HeadSemantics H head g D C (tables g)) :
    ∃ ys : List (∀ g,Moments.LabelValue (fun g=>(s g).label) g),
      ys.Nodup ∧ ys.toFinset=Finset.univ ∧ ys.map (familyInput s)=
        ((enumerate (List.ofFn tables)).map (Representative.bucket n)).reverse := by
  classical
  obtain ⟨ys,hn,hc,he⟩ := finalized_enumeration n tables (fun g=>(s g).input)
    (fun g=>(s g).input_injective) (fun g=>(s g).choices_mem) (fun g=>(s g).choices_nodup)
  exact ⟨ys,hn,full_toFinset ys hc,he⟩

end SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

end

end OAI.Algorithms
