import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblySemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgramValidity

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsAssembly
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
  (cache : RingProgram.ScalarCache p t) {n d : ℕ}
  (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
  (vars : Finset (Fin n)) (u J : ℕ)

abbrev ValidEntries {B d : ℕ} (entries : List (Product.Entry n B d)) : Prop :=
  ∀ a ∈ entries, Product.ValidKey vars u J a.1

theorem weightedValue_valid
    (weight : RingProgram.Code (Word (baseWidth p t)) d)
    (jet seed : List (Product.Entry n (baseWidth p t) d))
    (hj : ValidEntries vars u J jet) (hs : ValidEntries vars u J seed) :
    ValidEntries vars u J (weightedValue p t M cache table weight jet seed) := by
  apply Normalize.run_preserves_keys p t M cache (Product.ValidKey vars u J)
  · intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    exact hj b hb
  · exact hs

variable (meaning : AssignmentContext → List Bool → Contribution n (baseWidth p t) d)

theorem headRun_valid (c : AssignmentContext) (xs : List (List Bool))
    (seed : List (Product.Entry n (baseWidth p t) d))
    (hm : ∀ x ∈ xs, ValidEntries vars u J (meaning c x).2)
    (hs : ValidEntries vars u J seed) :
    ValidEntries vars u J (headRun p t M cache table meaning c xs seed) := by
  induction xs generalizing seed with
  | nil => exact hs
  | cons x xs ih =>
    exact ih _ (fun y hy => hm y (by simp [hy]))
      (weightedValue_valid p t M cache table vars u J _ _ seed (hm x (by simp)) hs)

theorem headStepValue_valid (high : Fin 768 → List Bool) (h : HeadInput)
    (left : List (Product.Entry n (baseWidth p t) d))
    (hm : ∀ x ∈ h.assignments, ValidEntries vars u J (meaning (headContext high h) x).2)
    (hl : ValidEntries vars u J left) :
    ValidEntries vars u J (headStepValue p t M cache table u J meaning high h left) := by
  apply Product.run_valid p t M cache table vars u J _ _ [] hl
  · exact headRun_valid p t M cache table vars u J meaning _ _ [] hm (by simp)
  · simp

theorem headsRun_valid (high : Fin 768 → List Bool) (hs : List HeadInput)
    (left : List (Product.Entry n (baseWidth p t) d))
    (hm : ∀ h ∈ hs, ∀ x ∈ h.assignments,
      ValidEntries vars u J (meaning (headContext high h) x).2)
    (hl : ValidEntries vars u J left) :
    ValidEntries vars u J (headsRun p t M cache table u J meaning high hs left) := by
  induction hs generalizing left with
  | nil => exact hl
  | cons h hs ih =>
    exact ih _ (fun k hk => hm k (by simp [hk]))
      (headStepValue_valid p t M cache table vars u J meaning high h left (hm h (by simp)) hl)

theorem rawProject_validEntries {B d : ℕ} (s : Finset (Fin n))
    (entries : List (Product.Entry n B d)) (he : ValidEntries vars u J entries) :
    ValidEntries vars u J (Moments.rawProject s entries) := by
  induction entries with
  | nil => simp [Moments.rawProject]
  | cons a entries ih =>
    have ha := he a (by simp)
    have ht := ih (fun b hb => he b (by simp [hb]))
    intro b hb
    by_cases h : a.1.vars = s
    · simp only [Moments.rawProject, h, ite_true, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ⟨ha.1, Nat.zero_le _, Finset.empty_subset _⟩
      · exact ht b hb
    · simp only [Moments.rawProject, h, ite_false] at hb
      exact ht b hb

theorem supportValue_valid (s : Finset (Fin n))
    (product seed : List (Product.Entry n (baseWidth p t) d))
    (hp : ValidEntries vars u J product) (hs : ValidEntries vars u J seed) :
    ValidEntries vars u J (supportValue p t M cache s product seed) :=
  Normalize.run_preserves_keys p t M cache (Product.ValidKey vars u J) _ seed
    (rawProject_validEntries vars u J s product hp) hs

theorem supportProduct_valid (high : Fin 768 → List Bool) (hs : List HeadInput)
    (one : List (Product.Entry n (baseWidth p t) d)) (s : Finset (Fin n))
    (hm : ∀ h ∈ hs, ∀ x ∈ h.assignments, ValidEntries vars u J
      (meaning (headContext (Function.update high 168 (encodeMask s)) h) x).2)
    (ho : ValidEntries vars u J one) :
    ValidEntries vars u J (supportProduct p t M cache table u J meaning high hs one s) :=
  headsRun_valid p t M cache table vars u J meaning _ hs one hm ho

theorem supportsRun_valid (high : Fin 768 → List Bool) (hs : List HeadInput)
    (one : List (Product.Entry n (baseWidth p t) d)) (ss : List (Finset (Fin n)))
    (seed : List (Product.Entry n (baseWidth p t) d))
    (hm : ∀ s ∈ ss, ∀ h ∈ hs, ∀ x ∈ h.assignments, ValidEntries vars u J
      (meaning (headContext (Function.update high 168 (encodeMask s)) h) x).2)
    (ho : ValidEntries vars u J one) (hi : ValidEntries vars u J seed) :
    ValidEntries vars u J (supportsRun p t M cache table u J meaning high hs one ss seed) := by
  induction ss generalizing seed with
  | nil => exact hi
  | cons s ss ih =>
    exact ih _ (fun q hq => hm q (by simp [hq]))
      (supportValue_valid p t M cache vars u J s _ seed
        (supportProduct_valid p t M cache table vars u J meaning high hs one s (hm s (by simp)) ho) hi)

theorem bucketsRun_valid (high : Fin 768 → List Bool) (ss : List (Finset (Fin n)))
    (one : List (Product.Entry n (baseWidth p t) d)) (bs : List BucketInput)
    (seed : List (Product.Entry n (baseWidth p t) d))
    (hm : ∀ b ∈ bs, ∀ s ∈ ss, ∀ h ∈ b.heads, ∀ x ∈ h.assignments, ValidEntries vars u J
      (meaning (headContext (Function.update (Function.update high 177 b.context)
        168 (encodeMask s)) h) x).2)
    (ho : ValidEntries vars u J one) (hi : ValidEntries vars u J seed) :
    ValidEntries vars u J (bucketsRun p t M cache table u J meaning high ss one bs seed) := by
  induction bs generalizing seed with
  | nil => exact hi
  | cons b bs ih =>
    exact ih _ (fun c hc => hm c (by simp [hc]))
      (supportsRun_valid p t M cache table vars u J meaning _ b.heads one ss seed (hm b (by simp)) ho hi)

variable {R : Type*} [CommRing R]
  (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)

/-- Turn an actual output dictionary into the checked abstract representation;
its data are the coefficient-wise decoding, without re-running the algorithm. -/
def stored (entries : List (Product.Entry n (baseWidth p t) d))
    (hv : ValidEntries vars u J entries) (hn : (Sparse.keys entries).Nodup) :
    Moments.Stored (R := R) vars u J :=
  ⟨Dictionary.denoteTable (coefficient p t M cache scalar basis) entries,
    Product.decoded_valid _ vars u J entries hv,
    by simpa only [Dictionary.denoteTable_keys] using hn⟩

@[simp] theorem stored_denote (entries : List (Product.Entry n (baseWidth p t) d))
    (hv : ValidEntries vars u J entries) (hn : (Sparse.keys entries).Nodup) :
    (stored p t M cache vars u J scalar basis entries hv hn).denote =
      denote p t M cache scalar basis entries := rfl

theorem valid_canonical (entries : List (Product.Entry n (baseWidth p t) d))
    (hv : ValidEntries vars u J entries) :
    canonical u J (denote p t M cache scalar basis entries) =
      denote p t M cache scalar basis entries :=
  (Product.decoded_valid (coefficient p t M cache scalar basis) vars u J entries hv).canonical

omit [Fact (Nat.Prime p)] in
theorem valid_length_le (entries : List (Product.Entry n (baseWidth p t) d))
    (hv : ValidEntries vars u J entries) (hn : (Sparse.keys entries).Nodup) :
    entries.length ≤ u * J * (Sparse.supportUniverse vars J).card := by
  have h := (Product.decoded_valid (fun _ => (0 : ℤ)) vars u J entries hv).length_le
    (by simpa only [Dictionary.denoteTable_keys] using hn)
  simpa [Dictionary.denoteTable] using h

end SubexponentialSAT.SqrtLog.MomentsAssembly

end OAI.Algorithms
