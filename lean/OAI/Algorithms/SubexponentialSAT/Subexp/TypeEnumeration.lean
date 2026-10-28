import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentAlphabetSemantics
import OAI.Algorithms.SubexponentialSAT.Subexp.FiberEnumeration

namespace OAI.Algorithms

/-!
# The actual universal-type enumeration

The byte list is the output of the fixed Cartesian-power program.  The
semantic list and its finite equivalences only name that same physical
order; they are not executable inputs to any program.
-/

namespace SubexponentialSAT.Subexp.TypeEnumeration

open MulticolorTypes
open CollisionProgram (encodeType registerWord)
open AssignmentAlphabetSemantics

def universalBytes (r Q Δ : ℕ) : List (List Bool) :=
  TupleProgram.powerRows (wordBytes r Q) (Δ + 1) [[]]

def ofWords {r Q Δ : ℕ} (v : Fin (Δ + 1) → Word r Q) : UniversalType r Q Δ :=
  ⟨v 0, fun i => v i.succ⟩

@[simp] theorem registerWord_ofWords {r Q Δ : ℕ} (v : Fin (Δ + 1) → Word r Q) :
    registerWord (ofWords v) = v := by
  funext a
  exact Fin.cases rfl (fun _ => rfl) a

@[simp] theorem ofWords_registerWord {r Q Δ : ℕ} (u : UniversalType r Q Δ) :
    ofWords (registerWord u) = u := by
  apply UniversalType.ext
  · rfl
  · funext i
    rfl

def wordCode {r Q : ℕ} (hr : 0 < r) (hQ : 0 < Q) : StackEncoding.BlockCode (Word r Q) where
  width := Q * r
  width_pos := Nat.mul_pos hQ hr
  block := ReadPlan.encodeWord
  length_block := ReadPlan.encodeWord_length
  injective_block := encodeWord_injective hr

theorem encodeTuple_eq {r Q Δ : ℕ} (hr : 0 < r) (hQ : 0 < Q)
    (v : Fin (Δ + 1) → Word r Q) :
    SubexpTupleRefinement.encodeTuple (wordCode hr hQ) v = encodeType (ofWords v) := by
  rw [ReadPlan.encodeType_eq_words, registerWord_ofWords]
  rw [SubexpTupleRefinement.encodeTuple, StackEncoding.encodeDataStack_eq_flatMap]
  rw [List.flatMap_def, List.map_ofFn]
  rfl

theorem universalBytes_nodup {r Q : ℕ} (hr : 0 < r) (hQ : 0 < Q) (Δ : ℕ) :
    (universalBytes r Q Δ).Nodup := by
  obtain ⟨a, tail, he, hn, _⟩ := wordBytes_order hr Q
  change (TupleProgram.powerRows (wordBytes r Q) (Δ + 1) [[]]).Nodup
  rw [← he]
  exact SubexpTupleRefinement.powerRows_encoded_nodup (wordCode hr hQ) (a :: tail) hn (Δ + 1)

theorem universalBytes_encode_mem {r Q Δ : ℕ} (hr : 0 < r) (hQ : 0 < Q)
    (u : UniversalType r Q Δ) : encodeType u ∈ universalBytes r Q Δ := by
  obtain ⟨a, tail, he, _, hf⟩ := wordBytes_order hr Q
  unfold universalBytes
  rw [← he]
  change encodeType u ∈
    TupleProgram.powerRows (List.map (wordCode hr hQ).block (a :: tail)) (Δ + 1) [[]]
  simpa only [encodeTuple_eq hr hQ, ofWords_registerWord] using
    SubexpTupleRefinement.encodeTuple_mem_powerRows (wordCode hr hQ)
      (a :: tail) hf (Δ + 1) (registerWord u)

theorem universalBytes_mem_encode {r Q Δ : ℕ} (hr : 0 < r) (hQ : 0 < Q)
    (bits : List Bool) (hb : bits ∈ universalBytes r Q Δ) :
    ∃ u : UniversalType r Q Δ, encodeType u = bits := by
  obtain ⟨a, tail, he, _, _⟩ := wordBytes_order hr Q
  unfold universalBytes at hb
  rw [← he] at hb
  obtain ⟨v, _, hv⟩ := (SubexpTupleRefinement.mem_powerRows_encoded
    (wordCode hr hQ) (a :: tail) (Δ + 1) bits).mp hb
  exact ⟨ofWords v, (encodeTuple_eq hr hQ v).symm.trans hv⟩

private theorem list_lift {A B : Type*} (f : A → B) (bs : List B)
    (h : ∀ b ∈ bs, ∃ a, f a = b) : ∃ as : List A, as.map f = bs := by
  induction bs with
  | nil => exact ⟨[], rfl⟩
  | cons b bs ih =>
      obtain ⟨a, ha⟩ := h b (by simp)
      obtain ⟨as, has⟩ := ih (by intro c hc; exact h c (by simp [hc]))
      exact ⟨a :: as, by simp [ha, has]⟩

theorem universalBytes_order {r Q : ℕ} (hr : 0 < r) (hQ : 0 < Q) (Δ : ℕ) :
    ∃ us : List (UniversalType r Q Δ), us.map encodeType = universalBytes r Q Δ ∧
      us.Nodup ∧ ∀ u, u ∈ us := by
  obtain ⟨us, he⟩ := list_lift encodeType (universalBytes r Q Δ)
    (universalBytes_mem_encode hr hQ)
  refine ⟨us, he, List.Nodup.of_map encodeType ?_, ?_⟩
  · rw [he]
    exact universalBytes_nodup hr hQ Δ
  · intro u
    have hu := universalBytes_encode_mem hr hQ u
    rw [← he, List.mem_map] at hu
    obtain ⟨v, hv, hve⟩ := hu
    exact CollisionProgram.encodeType_injective hve ▸ hv

/-- Proof-only names for the physical tuple order. -/
noncomputable def typeList {r Q : ℕ} (hr : 0 < r) (hQ : 0 < Q) (Δ : ℕ) :
    List (UniversalType r Q Δ) := Classical.choose (universalBytes_order hr hQ Δ)

theorem typeList_bytes {r Q : ℕ} (hr : 0 < r) (hQ : 0 < Q) (Δ : ℕ) :
    (typeList hr hQ Δ).map encodeType = universalBytes r Q Δ :=
  (Classical.choose_spec (universalBytes_order hr hQ Δ)).1

theorem typeList_nodup {r Q : ℕ} (hr : 0 < r) (hQ : 0 < Q) (Δ : ℕ) :
    (typeList hr hQ Δ).Nodup :=
  (Classical.choose_spec (universalBytes_order hr hQ Δ)).2.1

theorem mem_typeList {r Q Δ : ℕ} (hr : 0 < r) (hQ : 0 < Q) (u : UniversalType r Q Δ) :
    u ∈ typeList hr hQ Δ :=
  (Classical.choose_spec (universalBytes_order hr hQ Δ)).2.2 u

@[simp] theorem universalBytes_length (r Q Δ : ℕ) :
    (universalBytes r Q Δ).length = blockSize r Q Δ := by
  unfold universalBytes
  rw [TupleProgram.generated_count, wordBytes_length]
  simp only [blockSize, pow_mul]

theorem universalBytes_width {r Q Δ : ℕ} (hr : 0 < r) (hQ : 0 < Q)
    (bits : List Bool) (hb : bits ∈ universalBytes r Q Δ) :
    bits.length = CollisionProgram.typeWidth r Q Δ := by
  obtain ⟨u, rfl⟩ := universalBytes_mem_encode hr hQ bits hb
  exact CollisionProgram.encodeType_length u

def headIndex (r t g : ℕ) : ℕ := t * r + g
def slotIndex (r width t g i : ℕ) : ℕ := (i + 1) * width + headIndex r t g

def sideBytes (r Q Δ t g : ℕ) : List (List Bool) :=
  (universalBytes r Q Δ).filter (fun bits => bits.getD (headIndex r t g) false)

def jointBytes (r Q Δ t g i : ℕ) : List (List Bool) :=
  (sideBytes r Q Δ t g).filter (fun bits => !(bits.getD (slotIndex r (Q * r) t g i) false))

theorem encodeType_getD {r Q Δ : ℕ} (u : UniversalType r Q Δ)
    (a : Fin (Δ + 1)) (t : Fin Q) (g : Fin r) :
    (encodeType u).getD ((a.val * Q + t.val) * r + g.val) false =
      decide (registerWord u a t = g) := by
  have hv : (CollisionProgram.codeIndex a t g).val = (a.val * Q + t.val) * r + g.val := by
    simp [CollisionProgram.codeIndex,finProdFinEquiv]
    ring
  rw [← hv]
  simp [encodeType, List.getD_eq_getElem?_getD]

theorem encodeType_head {r Q Δ : ℕ} (u : UniversalType r Q Δ) (t : Fin Q) (g : Fin r) :
    (encodeType u).getD (headIndex r t.val g.val) false = decide (u.head t = g) := by
  rw [show headIndex r t.val g.val = ((0 : Fin (Δ + 1)).val * Q + t.val) * r + g.val by
    simp [headIndex]]
  rw [encodeType_getD, CollisionProgram.registerWord_zero]

theorem encodeType_slot {r Q Δ : ℕ} (u : UniversalType r Q Δ)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    (encodeType u).getD (slotIndex r (Q * r) t.val g.val i.val) false =
      decide (u.slot i t = g) := by
  have hi : slotIndex r (Q * r) t.val g.val i.val =
      (i.succ.val * Q + t.val) * r + g.val := by
    simp [slotIndex, headIndex, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
  rw [hi]
  simpa using encodeType_getD u i.succ t g

theorem subtypeList_map {A B : Type*} (p : A → Prop) [DecidablePred p]
    (xs : List A) (f : A → B) :
    (FiberEnumeration.subtypeList p xs).map (fun a => f a.val) =
      (xs.filter (fun a => decide (p a))).map f := by
  simp [FiberEnumeration.subtypeList, List.map_map, Function.comp_def]

noncomputable def sideList {r Q Δ : ℕ} (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) : List (Side (Δ := Δ) t g) :=
  FiberEnumeration.subtypeList (fun u => u ∈ side (Δ := Δ) t g) (typeList hr hQ Δ)

noncomputable def jointList {r Q Δ : ℕ} (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) : List (Joint t g i) :=
  FiberEnumeration.subtypeList (fun u => u ∈ joint t g i) (typeList hr hQ Δ)

theorem sideList_nodup {r Q Δ : ℕ} (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) :
    (sideList (Δ := Δ) hr hQ t g).Nodup :=
  FiberEnumeration.subtypeList_nodup _ _ (typeList_nodup hr hQ Δ)

theorem mem_sideList {r Q Δ : ℕ} (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (u : Side (Δ := Δ) t g) : u ∈ sideList hr hQ t g :=
  FiberEnumeration.mem_subtypeList _ _ u (mem_typeList hr hQ u.val)

theorem jointList_nodup {r Q Δ : ℕ} (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) : (jointList hr hQ t g i).Nodup :=
  FiberEnumeration.subtypeList_nodup _ _ (typeList_nodup hr hQ Δ)

theorem mem_jointList {r Q Δ : ℕ} (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) (u : Joint t g i) : u ∈ jointList hr hQ t g i :=
  FiberEnumeration.mem_subtypeList _ _ u (mem_typeList hr hQ u.val)

theorem sideList_bytes {r Q Δ : ℕ} (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) :
    (sideList (Δ := Δ) hr hQ t g).map (fun u => encodeType u.val) =
      sideBytes r Q Δ t.val g.val := by
  rw [sideList, subtypeList_map, sideBytes, ← typeList_bytes hr hQ Δ, List.filter_map]
  simp only [Function.comp_def, encodeType_head, mem_side]

theorem jointList_bytes {r Q Δ : ℕ} (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    (jointList hr hQ t g i).map (fun u => encodeType u.val) =
      jointBytes r Q Δ t.val g.val i.val := by
  rw [jointList, subtypeList_map, jointBytes, sideBytes, ← typeList_bytes hr hQ Δ]
  simp only [List.filter_map, List.filter_filter, Function.comp_def,
    encodeType_head, encodeType_slot, mem_joint]
  congr 2
  funext u
  by_cases hh : u.head t = g <;> by_cases hs : u.slot i t = g <;> simp [hh,hs]

noncomputable def sideEquiv {r Q Δ : ℕ} (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) :
    Fin (sideList (Δ := Δ) hr hQ t g).length ≃ Side (Δ := Δ) t g :=
  List.Nodup.getEquivOfForallMemList _ (sideList_nodup hr hQ t g) (mem_sideList hr hQ t g)

noncomputable def jointEquiv {r Q Δ : ℕ} (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    Fin (jointList hr hQ t g i).length ≃ Joint t g i :=
  List.Nodup.getEquivOfForallMemList _ (jointList_nodup hr hQ t g i) (mem_jointList hr hQ t g i)

end SubexponentialSAT.Subexp.TypeEnumeration

end OAI.Algorithms
