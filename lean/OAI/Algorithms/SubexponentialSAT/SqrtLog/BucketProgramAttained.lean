import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramSignedSemantics

namespace OAI.Algorithms

/-! The physically deduplicated key list has at most as many entries as the
attained exact integer signature range. This is the bridge to rank bounds;
serialized key lengths still depend on every supplied row. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

theorem attainedKeys_reverse_length (records : List Record) :
    (attainedKeys records.reverse).length=(attainedKeys records).length := by
  have he : (attainedKeys records.reverse).toFinset=(attainedKeys records).toFinset := by
    ext key
    simp
  have ha := List.toFinset_card_of_nodup (attainedKeys_nodup records.reverse)
  have hb := List.toFinset_card_of_nodup (attainedKeys_nodup records)
  rw [he] at ha
  omega

theorem attainedKeys_labelled_length_le {T : Type*} {h : ℕ}
    (W : List Bool) (rows : List (List (List Bool))) (js : List ℕ) (n : ℕ)
    (label : (Fin h → Bool) → T)
    (hlabel : ∀ x y,label x=label y →
      Label.key W (List.ofFn x) rows=Label.key W (List.ofFn y) rows) :
    (attainedKeys (Label.labelled W rows js n (assignments h))).length ≤
      Nat.card (Set.range label) := by
  classical
  let rs := Label.labelled W rows js n (assignments h)
  let ks := attainedKeys rs
  have hx : ∀ key : ks.toFinset,∃ x : Fin h → Bool,
      Label.key W (List.ofFn x) rows=key.val := by
    intro key
    have hk : key.val∈attainedKeys rs := List.mem_toFinset.mp key.property
    obtain ⟨payload,hp⟩ := (mem_attainedKeys rs key.val).mp hk
    obtain ⟨bits,hbits,he⟩ := List.mem_map.mp hp
    obtain ⟨x,rfl⟩ := assignments_sound hbits
    exact ⟨x,congrArg Prod.fst he⟩
  choose repr hrepr using hx
  let enc : ks.toFinset → Set.range label := fun key => ⟨label (repr key),⟨repr key,rfl⟩⟩
  have hinj : Function.Injective enc := by
    intro a b he
    apply Subtype.ext
    have hl : label (repr a)=label (repr b) := congrArg Subtype.val he
    exact (hrepr a).symm.trans ((hlabel _ _ hl).trans (hrepr b))
  have hc := Nat.card_le_card_of_injective enc hinj
  rw [Nat.card_eq_finsetCard,List.toFinset_card_of_nodup (attainedKeys_nodup rs)] at hc
  exact hc

/-- Applies to the full supplied row matrix, including zero and redundant
rows. No row independence premise or computed basis appears here. -/
theorem attainedKeys_length_le_signature_range {h d : ℕ}
    (W : List Bool) (c : Fin d → Fin h → List Bool) (A : Fin d → Fin h → ℤ)
    (js : List ℕ) (n : ℕ)
    (hc : ∀ j i,(SubexponentialSAT.BinaryArithmetic.toNat (c j i) : ℤ)=
      (SubexponentialSAT.BinaryArithmetic.toNat W : ℤ)+A j i) :
    (attainedKeys (Label.labelled W (List.ofFn (fun j => List.ofFn (c j)))
      js n (assignments h))).length ≤ Nat.card (Set.range (LayoutSignatureBound.boolSignature A)) := by
  apply attainedKeys_labelled_length_le W _ js n (LayoutSignatureBound.boolSignature A)
  intro x y he
  apply (signatureValue_exact_iff W c A x y hc).mpr
  intro j
  exact congrFun he j

theorem attainedKeys_signed_length_le_signature_range {h d : ℕ}
    (W : List Bool) (pairs : Fin d → Fin h → SignedWord) (A : Fin d → Fin h → ℤ)
    {ys : List (List (List Bool))} (js : List ℕ) (n : ℕ)
    (hy : List.Forall₂ (List.Forall₂ (shiftedWord W))
      (List.ofFn (fun j => List.ofFn (pairs j))) ys)
    (hN : ∀ j i,SubexponentialSAT.BinaryArithmetic.toNat (pairs j i).2 ≤ SubexponentialSAT.BinaryArithmetic.toNat W)
    (hA : ∀ j i,(SubexponentialSAT.BinaryArithmetic.toNat (pairs j i).1 : ℤ)-
      (SubexponentialSAT.BinaryArithmetic.toNat (pairs j i).2 : ℤ)=A j i) :
    (attainedKeys (Label.labelled W ys js n (assignments h))).length ≤
      Nat.card (Set.range (LayoutSignatureBound.boolSignature A)) := by
  obtain ⟨c,rfl,hc⟩ := shiftedMatrix_typed W pairs hy
  apply attainedKeys_length_le_signature_range W c A js n
  intro j i
  have hv := shiftedWord_integer W (pairs j i) (c j i) (hc j i) (hN j i)
  simpa only [hA j i] using hv

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
