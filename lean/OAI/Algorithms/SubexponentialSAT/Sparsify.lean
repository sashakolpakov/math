import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Encoding
import OAI.Algorithms.SubexponentialSAT.SunflowerBranch
import OAI.Algorithms.SubexponentialSAT.Sunflower
import OAI.Algorithms.SubexponentialSAT.InsertionInvariant
import OAI.Algorithms.SubexponentialSAT.SparsificationConstants
import OAI.Algorithms.SubexponentialSAT.BranchTree
import OAI.Algorithms.SubexponentialSAT.RemovalCharging

namespace OAI.Algorithms

/-!
# Deterministic sunflower sparsification

The selector enumerates fixed-cardinality subfamilies of the input and subclauses
of input clauses.  It uses the concrete syntax ordering from `Encoding`, rather
than a semantic choice oracle.  Recursive calls decrease total literal mass.
-/

namespace SubexponentialSAT.Sparsify

open SAT
open scoped BigOperators

variable {n : ℕ}

private def sortedClauses (F : CNF (Fin n)) : List (Clause (Fin n)) :=
  let r := fun C D : Clause (Fin n) => Encoding.clauseNumbers C ≤ Encoding.clauseNumbers D
  letI : IsTrans _ r := ⟨fun _ _ _ => le_trans⟩
  letI : Std.Total r := ⟨fun _ _ => le_total _ _⟩
  letI : Std.Antisymm r :=
    ⟨fun _ _ h h' => Encoding.clauseNumbers_injective (le_antisymm h h')⟩
  F.sort r

private def sortedFamilies (S : Finset (CNF (Fin n))) : List (CNF (Fin n)) :=
  let r := fun F G : CNF (Fin n) => Encoding.cnfNumbers F ≤ Encoding.cnfNumbers G
  letI : IsTrans _ r := ⟨fun _ _ _ => le_trans⟩
  letI : Std.Total r := ⟨fun _ _ => le_total _ _⟩
  letI : Std.Antisymm r :=
    ⟨fun _ _ h h' => Encoding.cnfNumbers_injective (le_antisymm h h')⟩
  S.sort r

@[simp] private theorem mem_sortedClauses (F : CNF (Fin n)) (C : Clause (Fin n)) :
    C ∈ sortedClauses F ↔ C ∈ F := by simp [sortedClauses]

@[simp] private theorem mem_sortedFamilies (S : Finset (CNF (Fin n))) (F : CNF (Fin n)) :
    F ∈ sortedFamilies S ↔ F ∈ S := by simp [sortedFamilies]

/-- Candidate cores are subclauses of existing clauses, not arbitrary subsets of
the entire variable universe. -/
def coreCandidates (F : CNF (Fin n)) : CNF (Fin n) :=
  F.biUnion Finset.powerset

def candidates (F : CNF (Fin n)) (z : ℕ → ℕ) (d : ℕ) :
    List (CNF (Fin n) × Clause (Fin n)) :=
  (sortedFamilies (F.powersetCard (z d))).flatMap fun G =>
    (sortedClauses (coreCandidates F)).map fun H => (G, H)

theorem coreCandidates_card_le (F : CNF (Fin n)) (k : ℕ) (hF : WidthAtMost k F) :
    (coreCandidates F).card ≤ F.card * 2 ^ k := by
  calc
    (coreCandidates F).card ≤ ∑ C ∈ F, C.powerset.card := Finset.card_biUnion_le
    _ ≤ ∑ _C ∈ F, 2 ^ k := by
      apply Finset.sum_le_sum
      intro C hC
      rw [Finset.card_powerset]
      exact Nat.pow_le_pow_right (by decide) (hF C hC)
    _ = F.card * 2 ^ k := by simp

/-- The finite selector searches polynomially many candidates for fixed width
and fixed sunflower thresholds. This is an enumeration-size bound, not a claim
about unimplemented Turing-machine bit costs. -/
theorem candidates_length_le (F : CNF (Fin n)) (z : ℕ → ℕ) (d k : ℕ)
    (hF : WidthAtMost k F) :
    (candidates F z d).length ≤ F.card ^ (z d + 1) * 2 ^ k := by
  have hlen : (candidates F z d).length =
      (F.card.choose (z d)) * (coreCandidates F).card := by
    simp [candidates, List.length_flatMap, sortedFamilies, sortedClauses,
      Finset.card_powersetCard ]
  rw [hlen]
  calc
    F.card.choose (z d) * (coreCandidates F).card ≤
        F.card ^ z d * (F.card * 2 ^ k) :=
      Nat.mul_le_mul (Nat.choose_le_pow _ _) (coreCandidates_card_le F k hF)
    _ = F.card ^ (z d + 1) * 2 ^ k := by rw [pow_succ]; ring

def Good (F : CNF (Fin n)) (z : ℕ → ℕ) (d : ℕ)
    (c : CNF (Fin n) × Clause (Fin n)) : Prop :=
  c.1 ⊆ F ∧ c.1.card = z d ∧ c.2.Nonempty ∧
    Sunflower.IsSunflowerWithCore c.1 c.2 ∧ ∀ C ∈ c.1, C.card = d

instance (F : CNF (Fin n)) (z : ℕ → ℕ) (d : ℕ)
    (c : CNF (Fin n) × Clause (Fin n)) : Decidable (Good F z d c) := by
  unfold Good Sunflower.IsSunflowerWithCore
  infer_instance

/-- A finite deterministic search, returning a proof of the tested predicate. -/
def pick {α : Type*} (P : α → Prop) [DecidablePred P] :
    List α → Option {a // P a}
  | [] => none
  | a :: as => if h : P a then some ⟨a, h⟩ else pick P as

theorem pick_none_iff {α : Type*} (P : α → Prop) [DecidablePred P] (as : List α) :
    pick P as = none ↔ ∀ a ∈ as, ¬ P a := by
  induction as with
  | nil => simp [pick]
  | cons a as ih =>
      by_cases h : P a <;> simp [pick, h, ih]

def findAtWidth (F : CNF (Fin n)) (z : ℕ → ℕ) (d : ℕ) :
    Option {c // Good F z d c} :=
  pick (Good F z d) (candidates F z d)

def FreeAt (F : CNF (Fin n)) (z : ℕ → ℕ) (d : ℕ) : Prop :=
  Sunflower.NonemptyCoreSunflowerFree (F.filter fun C => C.card = d) (z d)

theorem good_mem_candidates (F : CNF (Fin n)) (z : ℕ → ℕ) (d : ℕ)
    (hz : 2 ≤ z d) {c : CNF (Fin n) × Clause (Fin n)} (h : Good F z d c) :
    c ∈ candidates F z d := by
  rcases c with ⟨G, H⟩
  rcases h with ⟨hGF, hcard, hH, hflower, hwidth⟩
  change G.card = z d at hcard
  have hG : G.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨C, hCG⟩ := hG
  have hHC : H ⊆ C := hflower.1 C hCG
  have hcore : H ∈ coreCandidates F :=
    Finset.mem_biUnion.mpr ⟨C, hGF hCG, Finset.mem_powerset.mpr hHC⟩
  simp only [candidates, List.mem_flatMap, List.mem_map, mem_sortedFamilies,
    mem_sortedClauses]
  exact ⟨G, Finset.mem_powersetCard.mpr ⟨hGF, hcard⟩, H, hcore, rfl⟩

theorem findAtWidth_none_iff (F : CNF (Fin n)) (z : ℕ → ℕ) (d : ℕ)
    (hz : 2 ≤ z d) : findAtWidth F z d = none ↔ FreeAt F z d := by
  rw [findAtWidth, pick_none_iff]
  constructor
  · intro h G hG hcard H hH hflower
    have hgood : Good F z d (G, H) :=
      ⟨fun C hC => (Finset.mem_filter.mp (hG hC)).1, hcard, hH, hflower,
        fun C hC => (Finset.mem_filter.mp (hG hC)).2⟩
    exact h (G, H) (good_mem_candidates F z d hz hgood) hgood
  · intro h c _ hc
    rcases c with ⟨G, H⟩
    rcases hc with ⟨hGF, hcard, hH, hflower, hwidth⟩
    exact h G (fun C hC => Finset.mem_filter.mpr ⟨hGF hC, hwidth C hC⟩)
      hcard H hH hflower

/-- A chosen branch includes all of its independently checked local facts. -/
structure Choice (F : CNF (Fin n)) (z : ℕ → ℕ) (k : ℕ) where
  width : ℕ
  width_ge : 2 ≤ width
  width_le : width ≤ k
  flower : SunflowerBranch.Sunflower (Fin n) width
  present : SunflowerBranch.clauses flower.core flower.petals ⊆ F
  size : flower.petals.card = z width
  minimum : InsertionInvariant.MinimumWidth z F width

def Available (F : CNF (Fin n)) (z : ℕ → ℕ) (k d : ℕ) : Prop :=
  2 ≤ d ∧ d ≤ k ∧ (findAtWidth F z d).isSome = true

instance (F : CNF (Fin n)) (z : ℕ → ℕ) (k d : ℕ) :
    Decidable (Available F z k d) := by unfold Available; infer_instance

/-- Turn the first successful width search into all the branching data. -/
def leastChoice (F : CNF (Fin n)) (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d)
    (hex : ∃ d, Available F z k d) : Choice F z k := by
    let d := Nat.find hex
    have hd : Available F z k d := Nat.find_spec hex
    let c := (findAtWidth F z d).get hd.2.2
    rcases hc : c.val with ⟨G, H⟩
    have hg : Good F z d (G, H) := hc ▸ c.property
    let s := SunflowerBranch.Sunflower.ofClauses G H d hg.2.2.1
      (by simpa [hg.2.1] using hz d hd.1) hg.2.2.2.1.1
      hg.2.2.2.1.2 hg.2.2.2.2
    refine ⟨d, hd.1, hd.2.1, s, ?_, ?_, ?_⟩
    · simpa only [s, SunflowerBranch.Sunflower.ofClauses_selected] using hg.1
    · simpa only [s, SunflowerBranch.Sunflower.ofClauses,
        SunflowerBranch.petalFamily_card hg.2.2.2.1.1] using hg.2.1
    · intro j hj hjd
      apply (findAtWidth_none_iff F z j (hz j hj)).mp
      by_contra hn
      have hdk : d ≤ k := hd.2.1
      have hjA : Available F z k j :=
        ⟨hj, by omega, Option.isSome_iff_ne_none.mpr hn⟩
      have := Nat.find_min' hex hjA
      omega

/-- Select the least available width, then the first syntactic candidate. -/
def select (F : CNF (Fin n)) (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) : Option (Choice F z k) :=
  if h : ((Finset.range (k + 1)).filter (Available F z k)).Nonempty then
    some (leastChoice F z k hz
      (by obtain ⟨d, hd⟩ := h; exact ⟨d, (Finset.mem_filter.mp hd).2⟩))
  else none

theorem select_none_free (F : CNF (Fin n)) (z : ℕ → ℕ) (k : ℕ)
    (hz : ∀ d, 2 ≤ d → 2 ≤ z d) (h : select F z k hz = none)
    (d : ℕ) (hd : 2 ≤ d) (hdk : d ≤ k) : FreeAt F z d := by
  unfold select at h
  split_ifs at h with he
  apply (findAtWidth_none_iff F z d (hz d hd)).mp
  by_contra hn
  exact he ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
    hd, hdk, Option.isSome_iff_ne_none.mpr hn⟩⟩

namespace Choice

variable {F : CNF (Fin n)} {z : ℕ → ℕ} {k : ℕ}

def child (c : Choice F z k) (side : Bool) : CNF (Fin n) :=
  if side then SunflowerBranch.childB F c.flower.core c.flower.petals
  else SunflowerBranch.childA F c.flower.core c.flower.petals

def batch (c : Choice F z k) (side : Bool) : CNF (Fin n) :=
  if side then c.flower.petals else {c.flower.core}

theorem child_mass_lt (c : Choice F z k) (side : Bool) :
    SunflowerBranch.literalMass (c.child side) < SunflowerBranch.literalMass F := by
  cases side
  · exact c.flower.literalMass_childA_lt c.present
  · exact c.flower.literalMass_childB_lt c.present

theorem child_width (c : Choice F z k) (side : Bool) (hF : WidthAtMost k F) :
    WidthAtMost k (c.child side) := by
  cases side
  · exact c.flower.widthAtMost_childA hF c.present
  · exact c.flower.widthAtMost_childB hF c.present

theorem step (c : Choice F z k) (side : Bool) :
    RemovalCharging.SunflowerStep F (c.child side) (c.batch side) c.width := by
  cases side
  · exact .core c.flower c.present
  · exact .petals c.flower c.present

end Choice

/-- An actual finite binary decomposition tree. Leaf terminality is established
by the failed finite search, not assumed by the caller. -/
inductive Decomposition (z : ℕ → ℕ) (k : ℕ) : CNF (Fin n) → Type
  | leaf (F) (terminal : ∀ d, 2 ≤ d → d ≤ k → FreeAt F z d) : Decomposition z k F
  | branch {F} (choice : Choice F z k)
      (left : Decomposition z k (choice.child false))
      (right : Decomposition z k (choice.child true)) : Decomposition z k F

def build (z : ℕ → ℕ) (k : ℕ) (hz : ∀ d, 2 ≤ d → 2 ≤ z d)
    (F : CNF (Fin n)) : Decomposition z k F :=
  match h : select F z k hz with
  | none => .leaf F (select_none_free F z k hz h)
  | some c => .branch c (build z k hz (c.child false)) (build z k hz (c.child true))
termination_by SunflowerBranch.literalMass F
decreasing_by
  · exact c.child_mass_lt false
  · exact c.child_mass_lt true

namespace Decomposition

variable {z : ℕ → ℕ} {k : ℕ} {F : CNF (Fin n)}

def leaves : {F : CNF (Fin n)} → Decomposition z k F → List (CNF (Fin n))
  | _, .leaf F _ => [F]
  | _, .branch _ left right => left.leaves ++ right.leaves

def shape : {F : CNF (Fin n)} → Decomposition z k F → BranchTree.Tree
  | _, .leaf _ _ => .leaf
  | _, .branch _ left right => .branch left.shape right.shape

theorem covers (tree : Decomposition z k F) :
    Satisfiable F ↔ ∃ G ∈ tree.leaves, Satisfiable G := by
  induction tree with
  | leaf F ht => simp [leaves]
  | @branch F c left right ihL ihR =>
      simp only [leaves, List.mem_append, or_and_right, exists_or]
      rw [← ihL, ← ihR]
      exact SunflowerBranch.satisfiable_children_iff F c.flower.core c.flower.petals c.present

theorem leaf_width (tree : Decomposition z k F) (hF : WidthAtMost k F) :
    ∀ G ∈ tree.leaves, WidthAtMost k G := by
  induction tree with
  | leaf F ht => simpa [leaves] using hF
  | @branch F c left right ihL ihR =>
      intro G hG
      rcases List.mem_append.mp hG with h | h
      · exact ihL (c.child_width false hF) G h
      · exact ihR (c.child_width true hF) G h

theorem leaf_terminal (tree : Decomposition z k F) :
    ∀ G ∈ tree.leaves, ∀ d, 2 ≤ d → d ≤ k → FreeAt G z d := by
  induction tree with
  | leaf F ht => simpa [leaves] using ht
  | branch c left right ihL ihR =>
      intro G hG
      rcases List.mem_append.mp hG with h | h
      · exact ihL G h
      · exact ihR G h

theorem leaves_length_le_nodes (tree : Decomposition z k F) :
    tree.leaves.length ≤ tree.shape.nodeCount := by
  induction tree with
  | leaf F ht => simp [leaves, shape, BranchTree.Tree.nodeCount]
  | branch c left right ihL ihR =>
      simp only [leaves, List.length_append, shape, BranchTree.Tree.nodeCount]
      omega

end Decomposition

/-- Read a path as a total sequence of branch choices, false beyond its end. -/
def sideAt (p : List Bool) (t : ℕ) : Bool := decide (p[t]? = some true)

/-- Concrete histories extracted from a root-to-node path. All insertion
conditions are local branch facts; no cumulative bound is included here. -/
structure PathData (z : ℕ → ℕ) (k : ℕ) (F : CNF (Fin n)) (p : List Bool) where
  formula : ℕ → CNF (Fin n)
  inserted : ℕ → CNF (Fin n)
  width : ℕ → ℕ
  first : formula 0 = F
  step : ∀ t < p.length,
    RemovalCharging.SunflowerStep (formula t) (formula (t + 1)) (inserted t) (width t)
  minimum : ∀ t < p.length, InsertionInvariant.MinimumWidth z (formula t) (width t)
  lower : ∀ t < p.length, 2 ≤ width t
  upper : ∀ t < p.length, width t ≤ k
  bsize : ∀ t < p.length, sideAt p t = true → (inserted t).card = z (width t)

namespace PathData

variable {z : ℕ → ℕ} {k : ℕ} {F : CNF (Fin n)} {p : List Bool}

def empty (F : CNF (Fin n)) : PathData z k F [] where
  formula := fun _ => F
  inserted := fun _ => ∅
  width := fun _ => 0
  first := rfl
  step := by simp
  minimum := by simp
  lower := by simp
  upper := by simp
  bsize := by simp

def prepend (c : Choice F z k) (side : Bool) (tail : PathData z k (c.child side) p) :
    PathData z k F (side :: p) where
  formula := fun t => match t with | 0 => F | i + 1 => tail.formula i
  inserted := fun t => match t with | 0 => c.batch side | i + 1 => tail.inserted i
  width := fun t => match t with | 0 => c.width | i + 1 => tail.width i
  first := rfl
  step := by
    intro t ht
    cases t with
    | zero => simpa only [tail.first] using c.step side
    | succ t => exact tail.step t (by simpa using ht)
  minimum := by
    intro t ht
    cases t with
    | zero => exact c.minimum
    | succ t => exact tail.minimum t (by simpa using ht)
  lower := by
    intro t ht
    cases t with
    | zero => exact c.width_ge
    | succ t => exact tail.lower t (by simpa using ht)
  upper := by
    intro t ht
    cases t with
    | zero => exact c.width_le
    | succ t => exact tail.upper t (by simpa using ht)
  bsize := by
    intro t ht hs
    cases t with
    | zero =>
        cases side with
        | false => simp [sideAt] at hs
        | true => exact c.size
    | succ t =>
        exact tail.bsize t (by simpa using ht) (by simpa [sideAt] using hs)

end PathData

namespace Decomposition

variable {z : ℕ → ℕ} {k : ℕ} {F : CNF (Fin n)}

/-- Follow an actual path in the constructed tree and retain its local
sunflower transitions for the independent charging theorem. -/
def pathData : {F : CNF (Fin n)} → (tree : Decomposition z k F) →
    (p : List Bool) → p ∈ tree.shape.paths → PathData z k F p
  | F, _, [], _ => PathData.empty F
  | _, .leaf _ _, _ :: _, hp => False.elim (by simp [shape, BranchTree.Tree.paths] at hp)
  | _, .branch c left _, false :: p, hp =>
      PathData.prepend c false (pathData left p (by
        simpa [shape, BranchTree.Tree.paths] using hp))
  | _, .branch c _ right, true :: p, hp =>
      PathData.prepend c true (pathData right p (by
        simpa [shape, BranchTree.Tree.paths] using hp))

theorem path_budgets {M : ℕ} (tree : Decomposition (SparsificationConstants.z M) k F)
    (hM : 2 ≤ M) (hF : SunflowerBranch.Antichain F)
    (p : List Bool) (hp : p ∈ tree.shape.paths) :
    p.length ≤ SparsificationConstants.C M (k - 1) * n ∧ p.count true ≤ k * n / M := by
  let data := tree.pathData p hp
  have h := RemovalCharging.sunflower_path_budgets data.formula data.inserted data.width
    (sideAt p) M k hM (by simpa only [data.first] using hF)
    data.step data.minimum data.lower data.upper data.bsize
  have hs : ((Finset.range p.length).filter fun t => sideAt p t = true) =
      BranchTree.bPositions p := by
    ext t
    simp [sideAt, BranchTree.bPositions]
  rw [hs, BranchTree.card_bPositions_eq_count] at h
  exact h

theorem node_bound {M : ℕ} (tree : Decomposition (SparsificationConstants.z M) k F)
    (hk : 2 ≤ k) (hM : SparsificationConstants.Admissible k M)
    (hF : SunflowerBranch.Antichain F) :
    (tree.shape.nodeCount : ℝ) ≤
      (((SparsificationConstants.C M (k - 1) + 1) * (k + 1) * (n + 1) ^ 2 : ℕ) : ℝ) *
        (2 : ℝ) ^ ((n : ℝ) / 32) := by
  apply BranchTree.Tree.nodeCount_le_quadratic_exponential tree.shape k n M hk hM
  · intro p hp
    exact (tree.path_budgets hM.1 hF p hp).1
  · intro p hp
    exact (tree.path_budgets hM.1 hF p hp).2

end Decomposition

/-- Normalize once, then carry out the actual terminating branching algorithm. -/
def treeFor (M k : ℕ) (hM : 2 ≤ M) (F : CNF (Fin n)) :
    Decomposition (SparsificationConstants.z M) k (normalize F) :=
  build (SparsificationConstants.z M) k
    (fun d hd => SparsificationConstants.threshold_ge_two M d hM hd) (normalize F)

/-- All threshold parameters are selected from k before the input is examined. -/
def sparsifyTree (k : ℕ) (hk : 2 ≤ k) (F : CNF (Fin n)) :
    Decomposition (SparsificationConstants.z (SparsificationConstants.chooseM k hk))
      k (normalize F) :=
  treeFor (SparsificationConstants.chooseM k hk) k
    (SparsificationConstants.chooseM_spec k hk).1 F

/-- The explicit finite list returned by deterministic sunflower sparsification. -/
def sparsify (k : ℕ) (hk : 2 ≤ k) (F : CNF (Fin n)) : List (CNF (Fin n)) :=
  (sparsifyTree k hk F).leaves

theorem sparsify_correct (k : ℕ) (hk : 2 ≤ k) (F : CNF (Fin n)) :
    Satisfiable F ↔ ∃ G ∈ sparsify k hk F, Satisfiable G := by
  exact (satisfiable_normalize F).symm.trans (sparsifyTree k hk F).covers

theorem sparsify_width (k : ℕ) (hk : 2 ≤ k) (F : CNF (Fin n))
    (hF : WidthAtMost k F) : ∀ G ∈ sparsify k hk F, WidthAtMost k G :=
  (sparsifyTree k hk F).leaf_width (widthAtMost_of_subset (normalize_subset F) hF)

theorem sparsify_terminal (k : ℕ) (hk : 2 ≤ k) (F : CNF (Fin n)) :
    ∀ G ∈ sparsify k hk F, ∀ d, 2 ≤ d → d ≤ k →
      FreeAt G (SparsificationConstants.z (SparsificationConstants.chooseM k hk)) d :=
  (sparsifyTree k hk F).leaf_terminal

theorem sparsify_occurrence (k : ℕ) (hk : 2 ≤ k) (F : CNF (Fin n))
    (hF : WidthAtMost k F) : ∀ G ∈ sparsify k hk F,
      OccurrenceAtMost
        (SparsificationConstants.occurrenceCap (SparsificationConstants.chooseM k hk) k) G := by
  intro G hG
  apply Sunflower.terminal_occurrenceAtMost G (SparsificationConstants.chooseM k hk) k
    (SparsificationConstants.chooseM_spec k hk).1 (sparsify_width k hk F hF G hG)
  exact sparsify_terminal k hk F G hG

theorem sparsify_node_bound (k : ℕ) (hk : 2 ≤ k) (F : CNF (Fin n)) :
    ((sparsifyTree k hk F).shape.nodeCount : ℝ) ≤
      (((SparsificationConstants.C (SparsificationConstants.chooseM k hk) (k - 1) + 1) *
        (k + 1) * (n + 1) ^ 2 : ℕ) : ℝ) * (2 : ℝ) ^ ((n : ℝ) / 32) := by
  apply (sparsifyTree k hk F).node_bound hk (SparsificationConstants.chooseM_spec k hk)
  exact SunflowerBranch.antichain_absorb _

theorem sparsify_length_bound (k : ℕ) (hk : 2 ≤ k) (F : CNF (Fin n)) :
    ((sparsify k hk F).length : ℝ) ≤
      (((SparsificationConstants.C (SparsificationConstants.chooseM k hk) (k - 1) + 1) *
        (k + 1) * (n + 1) ^ 2 : ℕ) : ℝ) * (2 : ℝ) ^ ((n : ℝ) / 32) := by
  apply le_trans ?_ (sparsify_node_bound k hk F)
  exact_mod_cast (sparsifyTree k hk F).leaves_length_le_nodes

end SubexponentialSAT.Sparsify

end OAI.Algorithms
