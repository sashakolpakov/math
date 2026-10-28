import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CNFNormalize
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseAccumulatorProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseFrontierProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseControllerProgram

/-! Appendix A: the mathematical depth-first transition and its count invariant.

The transition below specifies a leaf operation by its exact count. It is not a
primitive implementation of that operation, and no bit-time bound is asserted.
The pending list retains the current node and one sibling per branch on the
active path; completed leaves are discarded immediately.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram

open SAT DisjointBranch
open scoped BigOperators

variable {n : ℕ}

structure Entry (n : ℕ) where
  formula : CNF (Fin n)
  depth : ℕ

structure State (n : ℕ) where
  pending : List (Entry n)
  total : ℕ

def initial (F : CNF (Fin n)) : State n := ⟨[⟨F, 0⟩], 0⟩

def step (M : ℕ) (s : State n) : State n :=
  match s.pending with
  | [] => s
  | node :: rest =>
    match SparsePriority.select node.formula M with
    | none => ⟨rest, s.total + count node.formula⟩
    | some (c, H) =>
      ⟨⟨childA node.formula c H, node.depth + 1⟩ ::
        ⟨childB node.formula c H, node.depth + 1⟩ :: rest, s.total⟩

def run (M : ℕ) : ℕ → State n → State n
  | 0, s => s
  | t + 1, s => step M (run M t s)

def mass (s : State n) : ℕ :=
  s.total + (s.pending.map fun e => count e.formula).sum

@[simp] theorem mass_initial (F : CNF (Fin n)) : mass (initial F) = count F := by
  simp [mass, initial]

/-- The count/frontier invariant does not depend on tie breaking. A physical
selector must separately certify sparsity and the sharp priority conditions. -/
inductive Transition : State n → State n → Prop
  | idle (total : ℕ) : Transition ⟨[], total⟩ ⟨[], total⟩
  | leaf (node : Entry n) (rest : List (Entry n)) (total : ℕ) :
      Transition ⟨node :: rest, total⟩ ⟨rest, total + count node.formula⟩
  | branch (node : Entry n) (rest : List (Entry n)) (total c : ℕ) (H : Clause (Fin n)) :
      Transition ⟨node :: rest, total⟩
        ⟨⟨childA node.formula c H, node.depth + 1⟩ ::
          ⟨childB node.formula c H, node.depth + 1⟩ :: rest, total⟩

theorem Transition.mass_eq {s t : State n} (h : Transition s t) : mass t = mass s := by
  cases h with
  | idle => rfl
  | leaf node rest total => simp [mass, Nat.add_assoc]
  | branch node rest total c H =>
    simp only [mass, List.map_cons, List.sum_cons]
    rw [count_children node.formula c H]
    omega

theorem step_transition (M : ℕ) (s : State n) : Transition s (step M s) := by
  rcases s with ⟨pending, total⟩
  cases pending with
  | nil => exact .idle total
  | cons node rest =>
    cases hselect : SparsePriority.select node.formula M with
    | none => simpa only [step, hselect] using Transition.leaf node rest total
    | some selected =>
      rcases selected with ⟨c, H⟩
      simpa only [step, hselect] using Transition.branch node rest total c H

theorem mass_step (M : ℕ) (s : State n) : mass (step M s) = mass s := by
  exact (step_transition M s).mass_eq

inductive Transitions : ℕ → State n → State n → Prop
  | refl (s : State n) : Transitions 0 s s
  | cons {s u t : State n} {steps : ℕ} : Transition s u →
      Transitions steps u t → Transitions (steps + 1) s t

theorem Transitions.trans {a b : ℕ} {s u t : State n}
    (h₁ : Transitions a s u) (h₂ : Transitions b u t) : Transitions (a + b) s t := by
  induction h₁ with
  | refl => simpa using h₂
  | @cons s v u a hs hv ih =>
    simpa only [Nat.add_assoc, Nat.add_comm 1 b] using Transitions.cons hs (ih h₂)

theorem Transitions.mass_eq {steps : ℕ} {s t : State n}
    (h : Transitions steps s t) : mass t = mass s := by
  induction h with
  | refl => rfl
  | cons hs ht ih => exact ih.trans hs.mass_eq

theorem Transitions.total_le_pow {steps : ℕ} {F : CNF (Fin n)} {s : State n}
    (h : Transitions steps (initial F) s) : s.total ≤ 2 ^ n := by
  have hm := h.mass_eq
  rw [mass_initial] at hm
  have hc : count F ≤ 2 ^ n := by simpa using count_le F
  unfold mass at hm
  omega

theorem Transitions.current_sum_le_pow {steps total : ℕ} {F : CNF (Fin n)}
    {node : Entry n} {rest : List (Entry n)}
    (h : Transitions steps (initial F) ⟨node :: rest, total⟩) :
    total + count node.formula ≤ 2 ^ n := by
  have hm := h.mass_eq
  rw [mass_initial] at hm
  have hc : count F ≤ 2 ^ n := by simpa using count_le F
  simp only [mass, List.map_cons, List.sum_cons] at hm
  omega

theorem Transitions.finished_count {steps : ℕ} {F : CNF (Fin n)} {s : State n}
    (h : Transitions steps (initial F) s) (hfinished : s.pending = []) :
    s.total = count F := by
  have hm := h.mass_eq
  simpa [mass, initial, hfinished] using hm

theorem mass_run (M t : ℕ) (s : State n) : mass (run M t s) = mass s := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run, mass_step, ih]

theorem total_run_le (M t : ℕ) (F : CNF (Fin n)) :
    (run M t (initial F)).total ≤ count F := by
  have h := mass_run M t (initial F)
  rw [mass_initial] at h
  unfold mass at h
  omega

theorem total_run_le_pow (M t : ℕ) (F : CNF (Fin n)) :
    (run M t (initial F)).total ≤ 2 ^ n :=
  (total_run_le M t F).trans (by simpa using count_le F)

theorem total_binary_length_le (M t : ℕ) (F : CNF (Fin n)) :
    (binaryNat (run M t (initial F)).total).length ≤ n + 1 :=
  binaryNat_length_le (total_run_le_pow M t F)

theorem total_eq_count_of_finished (M t : ℕ) (F : CNF (Fin n))
    (hfinished : (run M t (initial F)).pending = []) :
    (run M t (initial F)).total = count F := by
  have h := mass_run M t (initial F)
  rw [mass_initial] at h
  unfold mass at h
  rw [hfinished] at h
  simpa only [List.map_nil, List.sum_nil, Nat.add_zero] using h

/-- Every pending node has an actual sequence of selected disjoint branches.
This relation is proof evidence; it is not a stored history. -/
inductive Descendant (M : ℕ) (root : CNF (Fin n)) : ℕ → CNF (Fin n) → Prop
  | root : Descendant M root 0 root
  | left {d F c H} : Descendant M root d F →
      SparsePriority.select F M = some (c, H) →
      Descendant M root (d + 1) (childA F c H)
  | right {d F c H} : Descendant M root d F →
      SparsePriority.select F M = some (c, H) →
      Descendant M root (d + 1) (childB F c H)

theorem step_descendant (M : ℕ) (root : CNF (Fin n)) (s : State n)
    (hs : ∀ e ∈ s.pending, Descendant M root e.depth e.formula) :
    ∀ e ∈ (step M s).pending, Descendant M root e.depth e.formula := by
  rcases s with ⟨pending, total⟩
  cases pending with
  | nil => exact hs
  | cons node rest =>
    have hn := hs node (by simp)
    cases hselect : SparsePriority.select node.formula M with
    | none =>
      intro e he
      exact hs e (List.mem_cons_of_mem _ (by simpa [step, hselect] using he))
    | some selected =>
      rcases selected with ⟨c, H⟩
      intro e he
      simp only [step, hselect, List.mem_cons] at he
      rcases he with rfl | rfl | he
      · exact hn.left hselect
      · exact hn.right hselect
      · exact hs e (List.mem_cons_of_mem _ he)

theorem run_descendant (M t : ℕ) (F : CNF (Fin n)) :
    ∀ e ∈ (run M t (initial F)).pending, Descendant M F e.depth e.formula := by
  induction t with
  | zero =>
    intro e he
    simp only [run, initial, List.mem_singleton] at he
    subst e
    exact .root
  | succ t ih => exact step_descendant M F _ ih

theorem priority_literalMass_lt {M c : ℕ} {F : CNF (Fin n)} {H : Clause (Fin n)}
    (hM : 2 ≤ M) (hpriority : SparsePriority.Priority F M c H) :
    SunflowerBranch.literalMass (childA F c H) < SunflowerBranch.literalMass F ∧
      SunflowerBranch.literalMass (childB F c H) < SunflowerBranch.literalMass F := by
  obtain ⟨⟨C, hC, hc, hHC⟩, hpos, hproper, hdegree⟩ :=
    hpriority.spec
  have hsel : (selected F c H).Nonempty := ⟨C, mem_selected.mpr ⟨hC, hc, hHC⟩⟩
  have hpow : M ≤ M ^ (c - H.card) := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < M)
      (by omega : 1 ≤ c - H.card)
  exact ⟨literalMass_childA_lt hsel hproper,
    literalMass_childB_lt (Finset.card_pos.mp hpos) hproper
      (hM.trans (hpow.trans hdegree))⟩

theorem selected_literalMass_lt {M c : ℕ} {F : CNF (Fin n)} {H : Clause (Fin n)}
    (hM : 2 ≤ M) (hselect : SparsePriority.select F M = some (c, H)) :
    SunflowerBranch.literalMass (childA F c H) < SunflowerBranch.literalMass F ∧
      SunflowerBranch.literalMass (childB F c H) < SunflowerBranch.literalMass F :=
  priority_literalMass_lt hM (SparsePriority.select_has_priority (by omega) hselect)

theorem Descendant.depth_add_literalMass_le {M d : ℕ} {F G : CNF (Fin n)}
    (h : Descendant M F d G) (hM : 2 ≤ M) :
    d + SunflowerBranch.literalMass G ≤ SunflowerBranch.literalMass F := by
  induction h with
  | root => simp
  | @left d G c H hparent hselect ih =>
    have hm := (selected_literalMass_lt hM hselect).1
    omega
  | @right d G c H hparent hselect ih =>
    have hm := (selected_literalMass_lt hM hselect).2
    omega

def potential (s : State n) : ℕ :=
  (s.pending.map fun e => 3 ^ SunflowerBranch.literalMass e.formula).sum

private theorem two_powers_lt {a b c : ℕ} (ha : a < c) (hb : b < c) :
    3 ^ a + 3 ^ b < 3 ^ c := by
  cases c with
  | zero => omega
  | succ c =>
    have hpa := Nat.pow_le_pow_right (by decide : 0 < 3) (Nat.le_of_lt_succ ha)
    have hpb := Nat.pow_le_pow_right (by decide : 0 < 3) (Nat.le_of_lt_succ hb)
    have hp : 0 < 3 ^ c := Nat.pow_pos (by decide)
    rw [Nat.pow_succ]
    omega

theorem potential_step_lt (M : ℕ) (s : State n) (hM : 2 ≤ M)
    (hne : s.pending ≠ []) : potential (step M s) < potential s := by
  rcases s with ⟨pending, total⟩
  cases pending with
  | nil => exact (hne rfl).elim
  | cons node rest =>
    cases hselect : SparsePriority.select node.formula M with
    | none =>
      have hp : 0 < 3 ^ SunflowerBranch.literalMass node.formula :=
        Nat.pow_pos (by decide)
      simp only [step, hselect, potential, List.map_cons, List.sum_cons]
      omega
    | some selected =>
      rcases selected with ⟨c, H⟩
      obtain ⟨ha, hb⟩ := selected_literalMass_lt hM hselect
      have hp := two_powers_lt ha hb
      simp only [step, hselect, potential, List.map_cons, List.sum_cons]
      omega

theorem run_succ_start (M t : ℕ) (s : State n) :
    run M (t + 1) s = run M t (step M s) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change step M (run M (t + 1) s) = step M (run M t (step M s))
    rw [ih]

theorem run_add (M t u : ℕ) (s : State n) :
    run M (t + u) s = run M u (run M t s) := by
  induction u with
  | zero => rfl
  | succ u ih =>
    change step M (run M (t + u) s) = step M (run M u (run M t s))
    rw [ih]

/-- A termination bound for the semantic transition. This coarse bound does
not assert the draft's sharp running time or implement the leaf operation. -/
theorem exists_finished (M : ℕ) (s : State n) (hM : 2 ≤ M) :
    ∃ t ≤ potential s, (run M t s).pending = [] := by
  generalize hp : potential s = p
  induction p using Nat.strong_induction_on generalizing s with
  | h p ih =>
    by_cases hempty : s.pending = []
    · exact ⟨0, Nat.zero_le _, hempty⟩
    · have hlt : potential (step M s) < p := hp ▸ potential_step_lt M s hM hempty
      obtain ⟨t, ht, he⟩ := ih _ hlt (step M s) rfl
      refine ⟨t + 1, by omega, ?_⟩
      simpa only [run_succ_start] using he

theorem exists_finished_count (M : ℕ) (F : CNF (Fin n)) (hM : 2 ≤ M) :
    ∃ t ≤ 3 ^ SunflowerBranch.literalMass F,
      (run M t (initial F)).pending = [] ∧ (run M t (initial F)).total = count F := by
  obtain ⟨t, ht, he⟩ := exists_finished M (initial F) hM
  refine ⟨t, ?_, he, total_eq_count_of_finished M t F he⟩
  simpa [potential, initial] using ht

theorem first_finished (M bound : ℕ) (s : State n)
    (hfinished : (run M bound s).pending = []) :
    ∃ t ≤ bound, (run M t s).pending = [] ∧
      ∀ i < t, (run M i s).pending ≠ [] := by
  classical
  let hex : ∃ t, (run M t s).pending = [] := ⟨bound, hfinished⟩
  exact ⟨Nat.find hex, Nat.find_min' hex hfinished, Nat.find_spec hex,
    fun i hi => Nat.find_min hex hi⟩

/-- A proof-only tree records which concrete branches the selector makes.
The running state contains no such tree. -/
inductive Derivation (M : ℕ) : CNF (Fin n) → BranchTree.Tree → Prop
  | leaf {F} : SparsePriority.select F M = none → Derivation M F .leaf
  | branch {F c H A B} : SparsePriority.select F M = some (c, H) →
      Derivation M (childA F c H) A → Derivation M (childB F c H) B →
      Derivation M F (.branch A B)

theorem exists_derivation (M : ℕ) (F : CNF (Fin n)) (hM : 2 ≤ M) :
    ∃ tree, Derivation M F tree := by
  generalize hm : SunflowerBranch.literalMass F = m
  induction m using Nat.strong_induction_on generalizing F with
  | h m ih =>
    cases hselect : SparsePriority.select F M with
    | none => exact ⟨.leaf, .leaf hselect⟩
    | some selected =>
      rcases selected with ⟨c, H⟩
      obtain ⟨ha, hb⟩ := selected_literalMass_lt hM hselect
      obtain ⟨A, hA⟩ := ih _ (hm ▸ ha) (childA F c H) rfl
      obtain ⟨B, hB⟩ := ih _ (hm ▸ hb) (childB F c H) rfl
      exact ⟨.branch A B, .branch hselect hA hB⟩

/-- The macro transition visits each derivation node once, consumes its
frontier entry, and adds its exact count to the existing accumulator. -/
theorem Derivation.run_steps {M : ℕ} {F : CNF (Fin n)} {tree : BranchTree.Tree}
    (h : Derivation M F tree) (depth total : ℕ) (rest : List (Entry n)) :
    run M tree.nodeCount ⟨⟨F, depth⟩ :: rest, total⟩ =
      ⟨rest, total + count F⟩ := by
  induction h generalizing depth total rest with
  | leaf hselect => simp [BranchTree.Tree.nodeCount, run, step, hselect]
  | @branch F c H A B hselect hA hB ihA ihB =>
    have hfirst : step M ⟨⟨F, depth⟩ :: rest, total⟩ =
        ⟨⟨childA F c H, depth + 1⟩ :: ⟨childB F c H, depth + 1⟩ :: rest, total⟩ := by
      simp [step, hselect]
    rw [BranchTree.Tree.nodeCount, run_add, run_add]
    change run M B.nodeCount (run M A.nodeCount
      (step M ⟨⟨F, depth⟩ :: rest, total⟩)) = _
    rw [hfirst, ihA, ihB]
    congr 1
    rw [Nat.add_assoc, ← count_children F c H]

theorem Derivation.run_initial {M : ℕ} {F : CNF (Fin n)} {tree : BranchTree.Tree}
    (h : Derivation M F tree) :
    run M tree.nodeCount (initial F) = ⟨[], count F⟩ := by
  simpa [initial] using h.run_steps 0 0 []

theorem Derivation.selectedPaths {M : ℕ} {F : CNF (Fin n)} {tree : BranchTree.Tree}
    (h : Derivation M F tree) (hM : 0 < M) :
    ∀ p ∈ tree.paths, ∃ G, SparseCharging.SelectedPath M F p G := by
  induction h with
  | @leaf F hselect =>
    intro p hp
    simp only [BranchTree.Tree.paths, Finset.mem_singleton] at hp
    subst p
    exact ⟨F, .nil F⟩
  | @branch F c H A B hselect hA hB ihA ihB =>
    intro p hp
    simp only [BranchTree.Tree.paths, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact ⟨F, .nil F⟩
    · obtain ⟨G, hG⟩ := ihA q hq
      exact ⟨G, .step false (SparsePriority.select_has_priority hM hselect) hG⟩
    · obtain ⟨G, hG⟩ := ihB q hq
      exact ⟨G, .step true (SparsePriority.select_has_priority hM hselect) hG⟩

/-- The physical serialized search may use any fixed tie order satisfying the
source priority. This proof-only tree imposes no runtime storage obligation. -/
inductive PriorityDerivation (M : ℕ) : CNF (Fin n) → BranchTree.Tree → Prop
  | leaf {F} : SparsePriority.select F M = none → PriorityDerivation M F .leaf
  | branch {F c H A B} : SparsePriority.Priority F M c H →
      PriorityDerivation M (childA F c H) A → PriorityDerivation M (childB F c H) B →
      PriorityDerivation M F (.branch A B)

theorem Derivation.toPriority {M : ℕ} {F : CNF (Fin n)} {tree : BranchTree.Tree}
    (h : Derivation M F tree) (hM : 0 < M) : PriorityDerivation M F tree := by
  induction h with
  | leaf ht => exact .leaf ht
  | branch hs hA hB ihA ihB =>
    exact .branch (SparsePriority.select_has_priority hM hs) ihA ihB

theorem PriorityDerivation.selectedPaths {M : ℕ} {F : CNF (Fin n)} {tree : BranchTree.Tree}
    (h : PriorityDerivation M F tree) :
    ∀ p ∈ tree.paths, ∃ G, SparseCharging.SelectedPath M F p G := by
  induction h with
  | @leaf F ht =>
    intro p hp
    simp only [BranchTree.Tree.paths, Finset.mem_singleton] at hp
    subst p
    exact ⟨F, .nil F⟩
  | @branch F c H A B hp hA hB ihA ihB =>
    intro p hmem
    simp only [BranchTree.Tree.paths, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image] at hmem
    rcases hmem with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact ⟨F, .nil F⟩
    · obtain ⟨G, hG⟩ := ihA q hq
      exact ⟨G, .step false hp hG⟩
    · obtain ⟨G, hG⟩ := ihB q hq
      exact ⟨G, .step true hp hG⟩

theorem PriorityDerivation.transitions {M : ℕ} {F : CNF (Fin n)} {tree : BranchTree.Tree}
    (h : PriorityDerivation M F tree) (depth total : ℕ) (rest : List (Entry n)) :
    Transitions tree.nodeCount ⟨⟨F, depth⟩ :: rest, total⟩ ⟨rest, total + count F⟩ := by
  induction h generalizing depth total rest with
  | leaf ht => exact .cons (.leaf _ _ _) (.refl _)
  | @branch F c H A B hp hA hB ihA ihB =>
    have hs := Transitions.cons
      (Transition.branch ⟨F, depth⟩ rest total c H)
      ((ihA (depth + 1) total (⟨childB F c H, depth + 1⟩ :: rest)).trans
        (ihB (depth + 1) (total + count (childA F c H)) rest))
    simpa only [BranchTree.Tree.nodeCount, Nat.add_assoc, Nat.add_comm 1,
      ← count_children F c H] using hs

theorem PriorityDerivation.nodeCount_bound {F : CNF (Fin n)} {tree : BranchTree.Tree}
    (k : ℕ) (σ : ℚ) (hk : 2 ≤ k) (hσ : 0 < σ)
    (h : PriorityDerivation (SparseBudget.chooseForSigma k σ hσ) F tree)
    (hanti : SunflowerBranch.Antichain F) (hnt : ∀ C ∈ F, ¬ C.IsTautology)
    (hwidth : WidthAtMost k F) :
    (tree.nodeCount : ℝ) ≤
      ((SparseCharging.depthConstant k (SparseBudget.chooseForSigma k σ hσ) * n + 1 : ℕ) : ℝ) ^ 2 *
        (2 : ℝ) ^ ((σ : ℝ) * n) :=
  SparseBudget.selectedPaths_nodeCount_le tree F k σ hk hσ hanti hnt hwidth h.selectedPaths

/-- This bounds the number of macro visits. Charging each visit's searches,
leaf computation, and primitive storage is a separate obligation. -/
theorem exists_finished_visit_bound (F : CNF (Fin n)) (k : ℕ) (σ : ℚ)
    (hk : 2 ≤ k) (hσ : 0 < σ) (hanti : SunflowerBranch.Antichain F)
    (hnt : ∀ C ∈ F, ¬ C.IsTautology) (hwidth : WidthAtMost k F) :
    ∃ t : ℕ,
      run (SparseBudget.chooseForSigma k σ hσ) t (initial F) = ⟨[], count F⟩ ∧
      (t : ℝ) ≤
        ((SparseCharging.depthConstant k (SparseBudget.chooseForSigma k σ hσ) * n + 1 : ℕ) : ℝ) ^ 2 *
          (2 : ℝ) ^ ((σ : ℝ) * n) := by
  have hM : 2 ≤ SparseBudget.chooseForSigma k σ hσ :=
    (SparseBudget.chooseM_spec k σ.num.natAbs σ.den
      (SparseBudget.rational_data σ hσ).1).1
  obtain ⟨tree, ht⟩ := exists_derivation (SparseBudget.chooseForSigma k σ hσ) F hM
  exact ⟨tree.nodeCount, ht.run_initial,
    SparseBudget.selectedPaths_nodeCount_le tree F k σ hk hσ hanti hnt hwidth
      (ht.selectedPaths (by omega))⟩

theorem exists_normalized_finished_visit_bound (F : RawCNF n) (k : ℕ) (σ : ℚ)
    (hk : 2 ≤ k) (hσ : 0 < σ) (hwidth : ∀ C ∈ F, C.length ≤ k) :
    ∃ t : ℕ,
      run (SparseBudget.chooseForSigma k σ hσ) t
        (initial (normalize (ExecCNF.formulaSet F))) = ⟨[], rawCount F⟩ ∧
      (t : ℝ) ≤
        ((SparseCharging.depthConstant k (SparseBudget.chooseForSigma k σ hσ) * n + 1 : ℕ) : ℝ) ^ 2 *
          (2 : ℝ) ^ ((σ : ℝ) * n) := by
  obtain ⟨t, ht, hb⟩ := exists_finished_visit_bound
    (normalize (ExecCNF.formulaSet F)) k σ hk hσ
    (fun _ hC _ hD hCD => normalize_antichain hD hC hCD)
    (fun _ hC => normalize_not_tautology hC)
    (widthAtMost_of_subset (normalize_subset _) (formulaSet_width_le F hwidth))
  exact ⟨t, by simpa only [count_normalize, rawCount] using ht, hb⟩

/-- After the current node, sibling depths decrease strictly. -/
inductive Ordered : List (Entry n) → Prop
  | nil : Ordered []
  | cons (head : Entry n) (tail : List (Entry n))
      (strict : tail.Pairwise (fun a b => b.depth < a.depth))
      (bound : ∀ e ∈ tail, e.depth ≤ head.depth) : Ordered (head :: tail)

theorem ordered_tail {head : Entry n} {tail : List (Entry n)}
    (h : Ordered (head :: tail)) : Ordered tail := by
  cases h with
  | cons _ _ strict bound =>
    cases tail with
    | nil => exact .nil
    | cons e rest =>
      obtain ⟨hs, ht⟩ := List.pairwise_cons.mp strict
      exact .cons e rest ht (fun a ha => (hs a ha).le)

theorem ordered_step (M : ℕ) (s : State n) (h : Ordered s.pending) :
    Ordered (step M s).pending := by
  rcases s with ⟨pending, total⟩
  cases pending with
  | nil => exact h
  | cons node rest =>
    cases hselect : SparsePriority.select node.formula M with
    | none => simpa [step, hselect] using ordered_tail h
    | some selected =>
      rcases selected with ⟨c, H⟩
      cases h with
      | cons _ _ strict bound =>
        simp only [step, hselect]
        apply Ordered.cons
        · exact List.pairwise_cons.mpr
            ⟨fun e he => Nat.lt_succ_of_le (bound e he), strict⟩
        · intro e he
          simp only [List.mem_cons] at he
          rcases he with rfl | he
          · exact le_rfl
          · exact (bound e he).trans (Nat.le_succ _)

theorem Transition.ordered {s t : State n} (h : Transition s t)
    (hs : Ordered s.pending) : Ordered t.pending := by
  cases h with
  | idle => exact hs
  | leaf => exact ordered_tail hs
  | branch node rest total c H =>
    cases hs with
    | cons _ _ strict bound =>
      apply Ordered.cons
      · exact List.pairwise_cons.mpr
          ⟨fun e he => Nat.lt_succ_of_le (bound e he), strict⟩
      · intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact le_rfl
        · exact (bound e he).trans (Nat.le_succ _)

theorem Transitions.ordered {steps : ℕ} {s t : State n} (h : Transitions steps s t)
    (hs : Ordered s.pending) : Ordered t.pending := by
  induction h with
  | refl => exact hs
  | cons hstep hrest ih => exact ih (hstep.ordered hs)

theorem ordered_run (M t : ℕ) (F : CNF (Fin n)) :
    Ordered (run M t (initial F)).pending := by
  induction t with
  | zero => exact .cons _ [] .nil (by simp)
  | succ t ih => exact ordered_step M _ ih

private theorem strict_length_le (tail : List (Entry n)) (D : ℕ)
    (hs : tail.Pairwise (fun a b => b.depth < a.depth))
    (hb : ∀ e ∈ tail, e.depth < D) : tail.length ≤ D := by
  induction tail generalizing D with
  | nil => simp
  | cons e rest ih =>
    obtain ⟨hhead, hrest⟩ := List.pairwise_cons.mp hs
    have ht := ih e.depth hrest hhead
    have he := hb e (by simp)
    simpa using Nat.succ_le_of_lt (lt_of_le_of_lt ht he)

theorem ordered_length_le {pending : List (Entry n)} (D : ℕ)
    (ho : Ordered pending) (hd : ∀ e ∈ pending, e.depth ≤ D) :
    pending.length ≤ D + 2 := by
  cases ho with
  | nil => simp
  | cons head tail strict bound =>
    have ht := strict_length_le tail (D + 1) strict
      (fun e he => Nat.lt_succ_of_le (hd e (List.mem_cons_of_mem _ he)))
    simpa using Nat.succ_le_succ ht

/-- This uses a path-depth bound, rather than the total number of visited nodes. -/
theorem pending_length_le (M t D : ℕ) (F : CNF (Fin n))
    (hdepth : ∀ d G, Descendant M F d G → d ≤ D) :
    (run M t (initial F)).pending.length ≤ D + 2 :=
  ordered_length_le D (ordered_run M t F)
    (fun e he => hdepth e.depth e.formula (run_descendant M t F e he))

theorem pending_length_le_literalMass (M t : ℕ) (F : CNF (Fin n)) (hM : 2 ≤ M) :
    (run M t (initial F)).pending.length ≤ SunflowerBranch.literalMass F + 2 := by
  apply pending_length_le
  intro d G h
  have hm := h.depth_add_literalMass_le hM
  omega

theorem Descendant.widthAtMost {M d k : ℕ} {F G : CNF (Fin n)}
    (h : Descendant M F d G) (hF : WidthAtMost k F) : WidthAtMost k G := by
  induction h with
  | root => exact hF
  | @left d G c H hparent hselect ih =>
    obtain ⟨⟨C, hC, hc, hHC⟩, _, hproper, _⟩ := SparsePriority.select_spec hselect
    exact childA_widthAtMost ih ⟨C, mem_selected.mpr ⟨hC, hc, hHC⟩⟩ hproper
  | @right d G c H hparent hselect ih =>
    obtain ⟨⟨C, hC, hc, hHC⟩, hpos, hproper, _⟩ := SparsePriority.select_spec hselect
    exact childB_widthAtMost ih ⟨C, mem_selected.mpr ⟨hC, hc, hHC⟩⟩
      (Finset.card_pos.mp hpos) hproper

/-- A width-`k` set of clauses has polynomial-size explicit syntax. -/
def formulaBound (n k : ℕ) : ℕ :=
  n + 2 + (4 + (8 * n + 8) * k) * ((k + 1) * (2 * n + 1) ^ k)

theorem formulaBitLength_le (F : CNF (Fin n)) (k : ℕ) (hF : WidthAtMost k F) :
    Encoding.formulaBitLength F ≤ formulaBound n k :=
  (Encoding.formulaBitLength_upper F hF).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (SparsePriority.clause_card_le F k hF)) _)

/-- This is the actual callback body encoding, in its retained raw clause order. -/
def encodeBody (F : RawCNF n) : List Bool :=
  Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
    (F.map (List.map Encoding.literalCode))

theorem encodeBody_length_le (F : RawCNF n) (k : ℕ)
    (hC : ∀ C ∈ F, C.Nodup) (hF : (F.map ExecCNF.clauseSet).Nodup)
    (hwidth : WidthAtMost k (ExecCNF.formulaSet F)) :
    (encodeBody F).length ≤ formulaBound n k := by
  have h := formulaBitLength_le (ExecCNF.formulaSet F) k hwidth
  rw [Encoding.formulaBitLength_eq] at h
  rw [encodeBody, encodeRawCNFBody_length_eq F hC hF]
  omega

theorem encodeBody_normalize_length_le (F : RawCNF n) (k : ℕ)
    (hwidth : ∀ C ∈ F, C.length ≤ k) :
    (encodeBody (ExecCNF.normalize SAT.Literal.negate F)).length ≤ formulaBound n k := by
  apply encodeBody_length_le _ k (ExecCNF.normalize_literal_nodup _ _)
    (ExecCNF.normalize_map_nodup _ _)
  rw [ExecCNF.normalize_set]
  exact widthAtMost_of_subset (normalize_subset _) (formulaSet_width_le F hwidth)

/-- Pending bodies are stored once in a framed LIFO list; no count table or
completed-leaf list occurs in this representation. -/
def encodeFrontier (pending : List (RawCNF n)) : List Bool :=
  Encoding.encodeList encodeBody pending

theorem encodeFrontier_length_le (pending : List (RawCNF n)) (k D : ℕ)
    (hlen : pending.length ≤ D + 2)
    (hbodies : ∀ F ∈ pending, (encodeBody F).length ≤ formulaBound n k) :
    (encodeFrontier pending).length ≤
      1 + (2 * formulaBound n k + 2) * (D + 2) := by
  exact (Encoding.length_encodeList_upper encodeBody pending (formulaBound n k) hbodies).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hlen) 1)

theorem literalMass_le_card_mul (F : CNF (Fin n)) (k : ℕ) (hF : WidthAtMost k F) :
    SunflowerBranch.literalMass F ≤ F.card * k := by
  calc
    SunflowerBranch.literalMass F ≤ ∑ _C ∈ F, k := Finset.sum_le_sum hF
    _ = F.card * k := by simp

def encodeEntry (e : Entry n) : List Bool :=
  Encoding.encodeNat e.depth ++ Encoding.encodeCNF e.formula

def encodeState (s : State n) : List Bool :=
  Encoding.frame (binaryNat s.total) ++ Encoding.encodeList encodeEntry s.pending

/-- This bounds serialized semantic state, not the transient storage of a
primitive refinement of the transition. -/
theorem encodeState_run_length_le (M t D k : ℕ) (F : CNF (Fin n))
    (hF : WidthAtMost k F)
    (hdepth : ∀ d G, Descendant M F d G → d ≤ D) :
    (encodeState (run M t (initial F))).length ≤
      2 * (n + 1) + 2 + (2 * (D + 1 + formulaBound n k) + 2) * (D + 2) := by
  have hentry : ∀ e ∈ (run M t (initial F)).pending,
      (encodeEntry e).length ≤ D + 1 + formulaBound n k := by
    intro e he
    have hr := run_descendant M t F e he
    have hd := hdepth e.depth e.formula hr
    have hb := formulaBitLength_le e.formula k (hr.widthAtMost hF)
    simp only [encodeEntry, List.length_append, Encoding.length_encodeNat]
    change e.depth + 1 + Encoding.formulaBitLength e.formula ≤ _
    omega
  have hlist := Encoding.length_encodeList_upper encodeEntry
    (run M t (initial F)).pending (D + 1 + formulaBound n k) hentry
  have hlen := pending_length_le M t D F hdepth
  have htotal := total_binary_length_le M t F
  have hmul := Nat.mul_le_mul_left (2 * (D + 1 + formulaBound n k) + 2) hlen
  simp only [encodeState, List.length_append, Encoding.length_frame]
  omega

theorem encodeState_normalized_run_length_le (M t k : ℕ) (F : RawCNF n)
    (hM : 2 ≤ M) (hF : ∀ C ∈ F, C.length ≤ k) :
    (encodeState (run M t (initial (normalize (ExecCNF.formulaSet F))))).length ≤
      2 * (n + 1) + 2 +
        (2 * (F.length * k + 1 + formulaBound n k) + 2) * (F.length * k + 2) := by
  have hw := widthAtMost_of_subset (normalize_subset _) (formulaSet_width_le F hF)
  apply encodeState_run_length_le M t (F.length * k) k _ hw
  intro d G hG
  have hd := hG.depth_add_literalMass_le hM
  have hm := literalMass_le_card_mul (normalize (ExecCNF.formulaSet F)) k hw
  have hc := Nat.mul_le_mul_right k
    ((Finset.card_le_card (normalize_subset (ExecCNF.formulaSet F))).trans
      (formulaSet_card_le_length F))
  omega





theorem selectedPath_depth_add_literalMass_le {M : ℕ} {F G : CNF (Fin n)}
    {bits : List Bool} (hp : SparseCharging.SelectedPath M F bits G) (hM : 2 ≤ M) :
    bits.length + SunflowerBranch.literalMass G ≤ SunflowerBranch.literalMass F := by
  induction hp with
  | nil F => simp
  | @step F G bits c H b hpriority hp ih =>
    have hm := priority_literalMass_lt hM hpriority
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] at ih ⊢ <;> omega

theorem selectedPath_invariants {M k : ℕ} {F G : CNF (Fin n)}
    {bits : List Bool} (hp : SparseCharging.SelectedPath M F bits G)
    (hanti : SunflowerBranch.Antichain F)
    (hnt : ∀ C ∈ F, ¬ C.IsTautology) (hwidth : WidthAtMost k F) :
    SunflowerBranch.Antichain G ∧ (∀ C ∈ G, ¬ C.IsTautology) ∧ WidthAtMost k G := by
  revert hanti hnt hwidth
  induction hp with
  | nil F => exact fun ha hn hw => ⟨ha, hn, hw⟩
  | @step F G bits c H b hpriority hp ih =>
    intro ha hn hw
    obtain ⟨⟨C, hC, hc, hHC⟩, hpos, hproper, _⟩ := hpriority.spec
    have hsel : (selected F c H).Nonempty := ⟨C, mem_selected.mpr ⟨hC, hc, hHC⟩⟩
    cases b with
    | false =>
      apply ih (childA_antichain F c H) (childA_not_tautological hn hsel)
      exact childA_widthAtMost hw hsel hproper
    | true =>
      apply ih (childB_antichain F c H) (childB_not_tautological hn)
      exact childB_widthAtMost hw hsel (Finset.card_pos.mp hpos) hproper

theorem selectedPath_raw_depth_le (F : RawCNF n) {M k : ℕ}
    {G : CNF (Fin n)} {bits : List Bool}
    (hp : SparseCharging.SelectedPath M (normalize (ExecCNF.formulaSet F)) bits G)
    (hM : 2 ≤ M) (hwidth : ∀ C ∈ F, C.length ≤ k) :
    bits.length ≤ F.length * k := by
  have hw := widthAtMost_of_subset (normalize_subset _) (formulaSet_width_le F hwidth)
  have hd := selectedPath_depth_add_literalMass_le hp hM
  have hm := literalMass_le_card_mul (normalize (ExecCNF.formulaSet F)) k hw
  have hc := Nat.mul_le_mul_right k
    ((Finset.card_le_card (normalize_subset (ExecCNF.formulaSet F))).trans
      (formulaSet_card_le_length F))
  omega


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseCountProgram
