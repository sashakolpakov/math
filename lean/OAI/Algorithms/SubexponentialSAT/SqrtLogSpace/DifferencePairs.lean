import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.BooleanDifferences
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Pruned finite-difference traversal. `none`, `some false`, and `some true`
encode membership in neither set, in `E \ U`, and in `U`, respectively.
`words` specifies visit order; the streaming fold does not construct it. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairs

open scoped BigOperators
open BooleanDifferences

def words : ℕ → ℕ → List (List (Option Bool))
  | _, 0 => []
  | 0, _ + 1 => [[]]
  | n + 1, J + 1 =>
      (words n (J + 1)).map (none :: ·) ++
        (words n J).map (some false :: ·) ++
        (words n J).map (some true :: ·)

@[simp] theorem words_zero (n : ℕ) : words n 0 = [] := by cases n <;> rfl

@[simp] theorem mem_words (n J : ℕ) (w : List (Option Bool)) :
    w ∈ words n J ↔ w.length = n ∧ w.countP Option.isSome < J := by
  induction n generalizing J w with
  | zero =>
      cases J with
      | zero => simp [words]
      | succ J => cases w <;> simp [words]
  | succ n ih =>
      cases J with
      | zero => simp
      | succ J =>
          cases w with
          | nil => simp [words]
          | cons b w =>
              cases b with
              | none => simp [words, ih]
              | some b => cases b <;> simp [words, ih]

theorem words_nodup (n J : ℕ) : (words n J).Nodup := by
  induction n generalizing J with
  | zero => cases J <;> simp [words]
  | succ n ih =>
      cases J with
      | zero => simp
      | succ J =>
          simp only [words, List.nodup_append]
          refine ⟨⟨(ih (J + 1)).map (by intro a b h; exact List.cons.inj h |>.2),
            (ih J).map (by intro a b h; exact List.cons.inj h |>.2), ?_⟩,
            (ih J).map (by intro a b h; exact List.cons.inj h |>.2), ?_⟩
          · intro a ha b hb hab
            obtain ⟨u, _, rfl⟩ := List.mem_map.mp ha
            obtain ⟨v, _, rfl⟩ := List.mem_map.mp hb
            simp at hab
          · intro a ha b hb hab
            obtain ⟨v, _, rfl⟩ := List.mem_map.mp hb
            rcases List.mem_append.mp ha with ha | ha <;>
              obtain ⟨u, _, rfl⟩ := List.mem_map.mp ha <;>
              simp at hab

def pairCount : ℕ → ℕ → ℕ
  | _, 0 => 0
  | 0, _ + 1 => 1
  | n + 1, J + 1 => pairCount n (J + 1) + 2 * pairCount n J

@[simp] theorem pairCount_zero (n : ℕ) : pairCount n 0 = 0 := by cases n <;> rfl

@[simp] theorem words_length (n J : ℕ) : (words n J).length = pairCount n J := by
  induction n generalizing J with
  | zero => cases J <;> rfl
  | succ n ih =>
      cases J with
      | zero => rfl
      | succ J => simp [words, pairCount, ih]; omega

theorem pairCount_pos (n J : ℕ) (hJ : 0 < J) : 0 < pairCount n J := by
  have hw : List.replicate n none ∈ words n J := by simp [List.countP_replicate, hJ]
  rw [← words_length]
  exact List.length_pos_iff.mpr (by intro h; simp [h] at hw)

theorem pairCount_eq_sum (n J : ℕ) :
    pairCount n J = ∑ j ∈ Finset.range J, 2 ^ j * n.choose j := by
  have pascal (n J : ℕ) :
      (∑ j ∈ Finset.range (J + 1), 2 ^ j * (n + 1).choose j) =
        (∑ j ∈ Finset.range (J + 1), 2 ^ j * n.choose j) +
          2 * ∑ j ∈ Finset.range J, 2 ^ j * n.choose j := by
    induction J with
    | zero => simp
    | succ J ih =>
        rw [Finset.sum_range_succ _ (J + 1), ih,
          Nat.choose_succ_succ, Finset.sum_range_succ _ (J + 1),
          Finset.sum_range_succ _ J, pow_succ]
        ring
  induction n generalizing J with
  | zero =>
      cases J with
      | zero => simp
      | succ J => simp [pairCount, Finset.sum_range_succ']
  | succ n ih =>
      cases J with
      | zero => simp
      | succ J => rw [pairCount, ih, ih, pascal]

theorem pairFamily_card (n J : ℕ) : (pairFamily n J).card = pairCount n J := by
  rw [pairFamily_eq_biUnion]
  have disjoint : (↑(supportFamily n J) : Set (Finset (Fin n))).PairwiseDisjoint
      (fun E => E.powerset.image (fun U => (E, U))) := by
    intro E _ F _ hEF
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨U, _, hU⟩ := Finset.mem_image.mp hp
    obtain ⟨V, _, hV⟩ := Finset.mem_image.mp hq
    exact hEF (congrArg Prod.fst (hU.trans hV.symm))
  rw [Finset.card_biUnion disjoint]
  simp_rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),
    Finset.card_powerset]
  have hdisjoint : (↑(Finset.range J) : Set ℕ).PairwiseDisjoint
      (fun j => (Finset.univ : Finset (Fin n)).powersetCard j) := by
    intro i _ j _ hij
    exact Finset.disjoint_powersetCard_of_ne hij _ _
  have hs : supportFamily n J = (Finset.range J).disjiUnion
      (fun j => (Finset.univ : Finset (Fin n)).powersetCard j) hdisjoint := by
    ext E
    rw [mem_supportFamily, Finset.mem_disjiUnion]
    constructor
    · intro hE
      exact ⟨E.card, Finset.mem_range.mpr hE,
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ E, rfl⟩⟩
    · rintro ⟨j, hj, hE⟩
      exact (Finset.mem_powersetCard.mp hE).2 ▸ Finset.mem_range.mp hj
  rw [hs, Finset.sum_disjiUnion, pairCount_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h := Finset.sum_powersetCard j (Finset.univ : Finset (Fin n)) (fun a => 2 ^ a)
  rw [nsmul_eq_mul] at h
  simpa [Nat.mul_comm] using h

theorem pairCount_le_square (n J : ℕ) : pairCount n J ≤ (supportFamily n J).card ^ 2 := by
  rw [← pairFamily_card]
  exact pairFamily_card_le n J

def encodePair {n : ℕ} (E U : Finset (Fin n)) : List (Option Bool) :=
  List.ofFn (fun i => if i ∈ E then some (decide (i ∈ U)) else none)

theorem countP_ofFn {α : Type*} (p : α → Bool) (n : ℕ) (f : Fin n → α) :
    (List.ofFn f).countP p = ∑ i, if p (f i) then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.ofFn_succ, List.countP_cons, Fin.sum_univ_succ, ih]
      omega

@[simp] theorem encodePair_weight {n : ℕ} (E U : Finset (Fin n)) :
    (encodePair E U).countP Option.isSome = E.card := by
  rw [encodePair, countP_ofFn]
  have h (i : Fin n) :
      (if (if i ∈ E then some (decide (i ∈ U)) else none).isSome then 1 else 0) =
        (if i ∈ E then 1 else 0 : ℕ) := by
    by_cases hi : i ∈ E <;> simp [hi]
  simp_rw [h]
  simp

@[simp] theorem encodePair_outer_count {n : ℕ} (E U : Finset (Fin n)) :
    ((encodePair E U).map Option.isSome).reverse.count true = E.card := by
  simp [List.count_eq_countP, List.countP_map, Function.comp_def]

theorem encodePair_inner_count {n : ℕ} (E U : Finset (Fin n)) (hU : U ⊆ E) :
    ((encodePair E U).map (fun a => a.getD false)).reverse.count true = U.card := by
  have hm : (encodePair E U).map (fun a => a.getD false) =
      List.ofFn (fun i => decide (i ∈ U)) := by
    rw [encodePair, List.map_ofFn]
    congr 1
    funext i
    by_cases hi : i ∈ E
    · simp [hi]
    · have hu : i ∉ U := fun h => hi (hU h)
      simp [hi, hu]
  rw [hm, List.count_reverse, List.count_eq_countP, countP_ofFn]
  simp

theorem encodePair_injective {n : ℕ} {E U F V : Finset (Fin n)}
    (hU : U ⊆ E) (hV : V ⊆ F) (h : encodePair E U = encodePair F V) :
    E = F ∧ U = V := by
  have hf := List.ofFn_injective h
  have hE : E = F := by
    ext i
    have hi := congrArg Option.isSome (congrFun hf i)
    by_cases he : i ∈ E <;> by_cases hf : i ∈ F <;> simp_all
  subst F
  refine ⟨rfl, ?_⟩
  ext i
  have hi := congrFun hf i
  by_cases he : i ∈ E
  · simpa [he] using hi
  · have hu : i ∉ U := fun h => he (hU h)
    have hv : i ∉ V := fun h => he (hV h)
    simp [hu, hv]

theorem encoded_pairs_eq_words (n J : ℕ) :
    (pairFamily n J).image (fun p => encodePair p.1 p.2) = (words n J).toFinset := by
  have hsub : (pairFamily n J).image (fun p => encodePair p.1 p.2) ⊆
      (words n J).toFinset := by
    intro w hw
    obtain ⟨⟨E, U⟩, hEU, rfl⟩ := Finset.mem_image.mp hw
    simp only [List.mem_toFinset, mem_words]
    exact ⟨by simp [encodePair], by rw [encodePair_weight]; exact (mem_pairFamily.mp hEU).1⟩
  have hinj : Set.InjOn (fun p : Finset (Fin n) × Finset (Fin n) => encodePair p.1 p.2)
      (pairFamily n J : Set _) := by
    intro p hp q hq heq
    rcases p with ⟨E, U⟩
    rcases q with ⟨F, V⟩
    obtain ⟨rfl, rfl⟩ := encodePair_injective (mem_pairFamily.mp hp).2
      (mem_pairFamily.mp hq).2 heq
    rfl
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_image_iff.mpr hinj, List.toFinset_card_of_nodup (words_nodup n J),
    words_length, pairFamily_card]

def calls : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 1
  | n + 1, J + 1 => 1 + calls n (J + 1) + 2 * calls n J

@[simp] theorem calls_zero (n : ℕ) : calls n 0 = 1 := by cases n <;> rfl

theorem calls_le (n J : ℕ) (hJ : 0 < J) :
    calls n J ≤ (3 * n + 1) * pairCount n J := by
  induction n generalizing J with
  | zero => cases J <;> simp_all [calls, pairCount]
  | succ n ih =>
      cases J with
      | zero => omega
      | succ J =>
          have hl := ih (J + 1) (Nat.succ_pos J)
          have hp := pairCount_pos n (J + 1) (Nat.succ_pos J)
          cases J with
          | zero => simp only [calls, pairCount, calls_zero, pairCount_zero]; nlinarith
          | succ J =>
              have hr := ih (J + 1) (Nat.succ_pos J)
              simp only [calls, pairCount]
              nlinarith

/-- Runtime recursion retains one prefix and invokes its callback immediately.
The three branches share the accumulator; no list of completed pairs is built. -/
def fold {α : Type*} (visit : List (Option Bool) → α → α) :
    ℕ → ℕ → List (Option Bool) → α → α
  | _, 0, _, acc => acc
  | 0, _ + 1, pre, acc => visit pre acc
  | n + 1, J + 1, pre, acc =>
      let acc := fold visit n (J + 1) (pre ++ [none]) acc
      let acc := fold visit n J (pre ++ [some false]) acc
      fold visit n J (pre ++ [some true]) acc

theorem fold_eq_foldl {α : Type*} (visit : List (Option Bool) → α → α)
    (n J : ℕ) (pre : List (Option Bool)) (acc : α) :
    fold visit n J pre acc =
      (words n J).foldl (fun a w => visit (pre ++ w) a) acc := by
  induction n generalizing J pre acc with
  | zero => cases J <;> simp [fold, words]
  | succ n ih =>
      cases J with
      | zero => simp [fold]
      | succ J => simp [fold, words, ih, List.foldl_append, List.foldl_map]

/-- The reference visit order contains each admissible pair exactly once. -/
theorem sum_words_eq_sum_pairs {A : Type*} [AddCommMonoid A]
    (n J : ℕ) (f : List (Option Bool) → A) :
    ((words n J).map f).sum = ∑ p ∈ pairFamily n J, f (encodePair p.1 p.2) := by
  classical
  rw [← List.sum_toFinset f (words_nodup n J), ← encoded_pairs_eq_words]
  apply Finset.sum_image
  intro p hp q hq heq
  obtain ⟨he, hu⟩ := encodePair_injective (mem_pairFamily.mp hp).2
    (mem_pairFamily.mp hq).2 heq
  exact Prod.ext he hu

/-- A decoded accumulator may have a validity condition; it is retained at
all callback boundaries, while the decoded result is the exact pair sum. -/
theorem fold_decode_sum {A B : Type*} [AddCommMonoid B]
    (visit : List (Option Bool) → A → A) (decode : A → B) (P : A → Prop)
    (f : List (Option Bool) → B) (n J : ℕ) (acc : A) (ha : P acc)
    (step : ∀ w ∈ words n J, ∀ a, P a →
      P (visit w a) ∧ decode (visit w a) = decode a + f w) :
    P (fold visit n J [] acc) ∧
      decode (fold visit n J [] acc) =
        decode acc + ∑ p ∈ pairFamily n J, f (encodePair p.1 p.2) := by
  have hlist : ∀ (ws : List (List (Option Bool))) (a : A), P a →
      (∀ w ∈ ws, ∀ b, P b → P (visit w b) ∧ decode (visit w b) = decode b + f w) →
      P (ws.foldl (fun b w => visit w b) a) ∧
        decode (ws.foldl (fun b w => visit w b) a) = decode a + (ws.map f).sum := by
    intro ws
    induction ws with
    | nil => intro a ha _; exact ⟨ha, by simp⟩
    | cons w ws ih =>
        intro a ha hs
        obtain ⟨ha', he⟩ := hs w (by simp) a ha
        obtain ⟨hf, hv⟩ := ih (visit w a) ha' (fun v hv => hs v (by simp [hv]))
        refine ⟨hf, ?_⟩
        simpa [he, add_assoc] using hv
  simpa [fold_eq_foldl, sum_words_eq_sum_pairs] using hlist (words n J) acc ha step

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairs
