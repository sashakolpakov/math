import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Factor
import OAI.Algorithms.SubexponentialSAT.SAT
import OAI.Algorithms.SubexponentialSAT.BooleanPacking

namespace OAI.Algorithms

/-!
# Exact count preservation under finite coordinate encodings

This file constructs the validity and clause factors, rather than assuming
equality of their counts with the source problem.
-/

namespace SubexponentialSAT.FactorReduction

universe u v w z

def encode {V : Type u} {B : V → Type v} {A : Type w}
    (enc : (j : V) → B j ↪ A) (x : (j : V) → B j) : V → A :=
  fun j => enc j (x j)

theorem encode_injective {V : Type u} {B : V → Type v} {A : Type w}
    (enc : (j : V) → B j ↪ A) : Function.Injective (encode enc) := by
  intro x y h
  funext j
  exact (enc j).injective (congrFun h j)

def assignmentEmbedding {V : Type u} {B : V → Type v} {A : Type w}
    (enc : (j : V) → B j ↪ A) : ((j : V) → B j) ↪ (V → A) :=
  ⟨encode enc, encode_injective enc⟩

/-- A semantic image characterization gives an actual bijection of solutions. -/
noncomputable def solutionEquiv {X : Type u} {Y : Type v}
    (enc : X ↪ Y) (P : X → Prop) (Q : Y → Prop)
    (h : ∀ y, Q y ↔ ∃ x, enc x = y ∧ P x) :
    {x // P x} ≃ {y // Q y} :=
  Equiv.ofBijective
    (fun x => ⟨enc x, (h _).2 ⟨x, rfl, x.property⟩⟩)
    (by
      constructor
      · intro x y hxy
        apply Subtype.ext
        exact enc.injective (congrArg Subtype.val hxy)
      · intro y
        obtain ⟨x, hx, hp⟩ := (h y).1 y.property
        exact ⟨⟨x, hp⟩, Subtype.ext hx⟩)

theorem card_solutions {X : Type u} {Y : Type v} [Fintype X] [Fintype Y]
    (enc : X ↪ Y) (P : X → Prop) (Q : Y → Prop)
    [DecidablePred P] [DecidablePred Q]
    (h : ∀ y, Q y ↔ ∃ x, enc x = y ∧ P x) :
    Fintype.card {x // P x} = Fintype.card {y // Q y} :=
  Fintype.card_congr (solutionEquiv enc P Q h)

abbrev LocalAssignment {V : Type u} (B : V → Type v) (s : Finset V) :=
  (j : {j // j ∈ s}) → B j.val

def SourceSatisfies {V : Type u} {E : Type z} {B : V → Type v}
    (scope : E → Finset V)
    (table : (e : E) → LocalAssignment B (scope e) → Bool)
    (x : (j : V) → B j) : Prop :=
  ∀ e, table e (fun j => x j.val) = true

/-- The unary checks and the encoded local clause checks. -/
def EncodedSatisfies {V : Type u} {E : Type z} {B : V → Type v} {A : Type w}
    (enc : (j : V) → B j ↪ A) (scope : E → Finset V)
    (table : (e : E) → LocalAssignment B (scope e) → Bool)
    (x : V → A) : Prop :=
  (∀ j, ∃ b, enc j b = x j) ∧
    ∀ e, ∃ vals : LocalAssignment B (scope e),
      table e vals = true ∧ ∀ j, enc j.val (vals j) = x j.val

theorem encodedSatisfies_iff {V : Type u} {E : Type z}
    {B : V → Type v} {A : Type w}
    (enc : (j : V) → B j ↪ A) (scope : E → Finset V)
    (table : (e : E) → LocalAssignment B (scope e) → Bool) (x : V → A) :
    EncodedSatisfies enc scope table x ↔
      ∃ y, encode enc y = x ∧ SourceSatisfies scope table y := by
  constructor
  · rintro ⟨hvalid, hclauses⟩
    choose y hy using hvalid
    refine ⟨y, funext hy, ?_⟩
    intro e
    obtain ⟨vals, hlocal, henc⟩ := hclauses e
    have heq : vals = fun j : {j // j ∈ scope e} => y j.val := by
      funext j
      apply (enc j.val).injective
      exact (henc j).trans (hy j.val).symm
    rwa [heq] at hlocal
  · rintro ⟨y, rfl, hy⟩
    constructor
    · intro j
      exact ⟨y j, rfl⟩
    · intro e
      exact ⟨(fun j => y j.val), hy e, fun _ => rfl⟩

theorem encoded_card_preservation {V : Type u} {E : Type z}
    {B : V → Type v} {A : Type w}
    [Fintype V] [∀ j, Fintype (B j)] [Fintype A]
    (enc : (j : V) → B j ↪ A) (scope : E → Finset V)
    (table : (e : E) → LocalAssignment B (scope e) → Bool) :
    Nat.card {y // SourceSatisfies scope table y} =
      Nat.card {x // EncodedSatisfies enc scope table x} := by
  exact Nat.card_congr
    (solutionEquiv (assignmentEmbedding enc) (SourceSatisfies scope table)
      (EncodedSatisfies enc scope table) (encodedSatisfies_iff enc scope table))

/-- Each original coordinate receives one unary factor in addition to the
original local constraints. -/
def factorScope {V : Type u} {E : Type z} [DecidableEq V]
    (scope : E → Finset V) : V ⊕ E → Finset V
  | .inl j => {j}
  | .inr e => scope e

/-- An explicit finite table construction. All existential searches range over
finite source alphabets; there is no unbounded semantic oracle. -/
noncomputable def factorTable {V : Type u} {E : Type z} {B : V → Type v} {A : Type w}
    [DecidableEq V] [∀ j, Fintype (B j)] [DecidableEq A]
    (enc : (j : V) → B j ↪ A) (scope : E → Finset V)
    (table : (e : E) → LocalAssignment B (scope e) → Bool) :
    (e : V ⊕ E) → ({j // j ∈ factorScope scope e} → A) → Bool
  | .inl j, x => decide (∃ b, enc j b = x ⟨j, by simp [factorScope]⟩)
  | .inr e, x => by
      classical
      exact decide (∃ vals : LocalAssignment B (scope e),
        table e vals = true ∧ ∀ j, enc j.val (vals j) = x j)

theorem all_factorTable_iff {V : Type u} {E : Type z}
    {B : V → Type v} {A : Type w}
    [DecidableEq V] [∀ j, Fintype (B j)] [DecidableEq A]
    (enc : (j : V) → B j ↪ A) (scope : E → Finset V)
    (table : (e : E) → LocalAssignment B (scope e) → Bool) (x : V → A) :
    (∀ e, factorTable enc scope table e (fun j => x j.val) = true) ↔
      EncodedSatisfies enc scope table x := by
  constructor
  · intro h
    constructor
    · intro j
      simpa only [factorTable, decide_eq_true_eq] using h (.inl j)
    · intro e
      simpa only [factorTable, decide_eq_true_eq] using h (.inr e)
  · rintro ⟨hu, hc⟩ e
    cases e with
    | inl j => simpa only [factorTable, decide_eq_true_eq] using hu j
    | inr e => simpa only [factorTable, decide_eq_true_eq] using hc e

/-- A genuine finite factor system with one unary validity table per coordinate. -/
noncomputable def factorSystem {V : Type u} {E : Type z} {B : V → Type v} {A : Type w}
    [DecidableEq V] [∀ j, Fintype (B j)] [DecidableEq A]
    (enc : (j : V) → B j ↪ A) (scope : E → Finset V)
    (table : (e : E) → LocalAssignment B (scope e) → Bool) :
    Factor.System V (V ⊕ E) A where
  scope := factorScope scope
  table := factorTable enc scope table

theorem factorSystem_satisfies_iff {V : Type u} {E : Type z}
    {B : V → Type v} {A : Type w}
    [DecidableEq V] [∀ j, Fintype (B j)] [DecidableEq A]
    (enc : (j : V) → B j ↪ A) (scope : E → Finset V)
    (table : (e : E) → LocalAssignment B (scope e) → Bool) (x : V → A) :
    Factor.Satisfies (factorSystem enc scope table) x ↔
      ∃ y, encode enc y = x ∧ SourceSatisfies scope table y := by
  exact (all_factorTable_iff enc scope table x).trans
    (encodedSatisfies_iff enc scope table x)

theorem factorSystem_count {V : Type u} {E : Type z}
    {B : V → Type v} {A : Type w}
    [DecidableEq V] [Fintype V] [Fintype E]
    [∀ j, Fintype (B j)] [DecidableEq A] [Fintype A]
    (enc : (j : V) → B j ↪ A) (scope : E → Finset V)
    (table : (e : E) → LocalAssignment B (scope e) → Bool) :
    Factor.count (factorSystem enc scope table) =
      Nat.card {y // SourceSatisfies scope table y} := by
  classical
  rw [Factor.count_eq_card_subtype]
  have h := Nat.card_congr
    (solutionEquiv (assignmentEmbedding enc) (SourceSatisfies scope table)
      (Factor.Satisfies (factorSystem enc scope table))
      (factorSystem_satisfies_iff enc scope table)).symm
  simpa only [Nat.card_eq_fintype_card] using h

section CNF

variable {V : Type u} {J : Type v} [DecidableEq V] [DecidableEq J]
variable {b : J → ℕ}

/-- Reassemble all chunk bits using an explicit partition of the variables. -/
def assignmentFromChunks (positions : V ≃ (j : J) × Fin (b j))
    (x : (j : J) → Fin (b j) → Bool) : SAT.Assignment V :=
  fun v => x (positions v).1 (positions v).2

def chunkAssignmentEquiv (positions : V ≃ (j : J) × Fin (b j)) :
    ((j : J) → Fin (b j) → Bool) ≃ SAT.Assignment V where
  toFun := assignmentFromChunks positions
  invFun := fun a j i => a (positions.symm ⟨j, i⟩)
  left_inv := by
    intro x
    funext j i
    change (fun s : (j : J) × Fin (b j) => x s.1 s.2)
      (positions (positions.symm ⟨j, i⟩)) = x j i
    rw [positions.apply_symm_apply]
  right_inv := by
    intro a
    funext v
    simp [assignmentFromChunks]

/-- A clause touches exactly the chunks containing one of its variables. -/
def cnfScope (positions : V ≃ (j : J) × Fin (b j)) (F : SAT.CNF V) :
    {C // C ∈ F} → Finset J :=
  fun C => C.val.image (fun l => (positions l.variable).1)

omit [DecidableEq V] in
theorem cnfScope_card_le (positions : V ≃ (j : J) × Fin (b j))
    (F : SAT.CNF V) (C : {C // C ∈ F}) :
    (cnfScope positions F C).card ≤ C.val.card :=
  Finset.card_image_le

omit [DecidableEq V] in
theorem cnfScope_nonempty_iff (positions : V ≃ (j : J) × Fin (b j))
    (F : SAT.CNF V) (C : {C // C ∈ F}) :
    (cnfScope positions F C).Nonempty ↔ C.val.Nonempty :=
  Finset.image_nonempty

/-- Off-scope variables are assigned false only to make clause evaluation total;
the next theorem proves these default values are never read by the clause. -/
def cnfTable (positions : V ≃ (j : J) × Fin (b j)) (F : SAT.CNF V)
    (C : {C // C ∈ F})
    (x : LocalAssignment (fun j => Fin (b j) → Bool) (cnfScope positions F C)) : Bool :=
  C.val.eval (fun v => if h : (positions v).1 ∈ cnfScope positions F C then
    x ⟨(positions v).1, h⟩ (positions v).2 else false)

omit [DecidableEq V] in
theorem cnfTable_true_iff (positions : V ≃ (j : J) × Fin (b j))
    (F : SAT.CNF V) (C : {C // C ∈ F}) (x : (j : J) → Fin (b j) → Bool) :
    cnfTable positions F C (fun j => x j.val) = true ↔
      C.val.eval (assignmentFromChunks positions x) = true := by
  simp only [cnfTable, SAT.Clause.eval_eq_true, SAT.Literal.eval_eq_true]
  constructor
  · rintro ⟨l, hl, hv⟩
    refine ⟨l, hl, ?_⟩
    have hmem : (positions l.variable).1 ∈ cnfScope positions F C :=
      Finset.mem_image.mpr ⟨l, hl, rfl⟩
    simpa only [hmem, dite_eq_left, assignmentFromChunks] using hv
  · rintro ⟨l, hl, hv⟩
    refine ⟨l, hl, ?_⟩
    have hmem : (positions l.variable).1 ∈ cnfScope positions F C :=
      Finset.mem_image.mpr ⟨l, hl, rfl⟩
    simpa only [hmem, dite_eq_left, assignmentFromChunks] using hv

omit [DecidableEq V] in
theorem sourceSatisfies_cnf_iff (positions : V ≃ (j : J) × Fin (b j))
    (F : SAT.CNF V) (x : (j : J) → Fin (b j) → Bool) :
    SourceSatisfies (cnfScope positions F) (cnfTable positions F) x ↔
      F.eval (assignmentFromChunks positions x) = true := by
  simp only [SourceSatisfies, cnfTable_true_iff, SAT.CNF.eval_eq_true]
  constructor
  · intro h C hC
    exact h ⟨C, hC⟩
  · intro h C
    exact h C.val C.property

def cnfSourceSolutionEquiv (positions : V ≃ (j : J) × Fin (b j))
    (F : SAT.CNF V) :
    {x // SourceSatisfies (cnfScope positions F) (cnfTable positions F) x} ≃
      {a : SAT.Assignment V // F.eval a = true} :=
  (chunkAssignmentEquiv positions).subtypeEquiv (sourceSatisfies_cnf_iff positions F)

/-- Actual CNF-to-factor reduction for any injective encoding of each chunk. -/
noncomputable def cnfFactorSystem {A : Type w} [DecidableEq A]
    (positions : V ≃ (j : J) × Fin (b j))
    (enc : (j : J) → (Fin (b j) → Bool) ↪ A) (F : SAT.CNF V) :
    Factor.System J (J ⊕ {C // C ∈ F}) A :=
  factorSystem enc (cnfScope positions F) (cnfTable positions F)

def cnfAssignmentEmbedding {A : Type w}
    (positions : V ≃ (j : J) × Fin (b j))
    (enc : (j : J) → (Fin (b j) → Bool) ↪ A) : SAT.Assignment V ↪ (J → A) :=
  (chunkAssignmentEquiv positions).symm.toEmbedding.trans (assignmentEmbedding enc)

omit [DecidableEq V] in
theorem cnfFactorSystem_satisfies_iff {A : Type w} [DecidableEq A]
    (positions : V ≃ (j : J) × Fin (b j))
    (enc : (j : J) → (Fin (b j) → Bool) ↪ A) (F : SAT.CNF V) (x : J → A) :
    Factor.Satisfies (cnfFactorSystem positions enc F) x ↔
      ∃ a : SAT.Assignment V, cnfAssignmentEmbedding positions enc a = x ∧
        F.eval a = true := by
  rw [cnfFactorSystem, factorSystem_satisfies_iff]
  constructor
  · rintro ⟨y, hy, hs⟩
    refine ⟨chunkAssignmentEquiv positions y, ?_,
      (sourceSatisfies_cnf_iff positions F y).1 hs⟩
    change encode enc ((chunkAssignmentEquiv positions).symm
      (chunkAssignmentEquiv positions y)) = x
    simpa using hy
  · rintro ⟨a, ha, hs⟩
    refine ⟨(chunkAssignmentEquiv positions).symm a, ha, ?_⟩
    apply (sourceSatisfies_cnf_iff positions F _).2
    change F.eval (chunkAssignmentEquiv positions
      ((chunkAssignmentEquiv positions).symm a)) = true
    simpa using hs

theorem cnfFactorSystem_count {A : Type w} [DecidableEq A] [Fintype A]
    [Fintype V] [Fintype J]
    (positions : V ≃ (j : J) × Fin (b j))
    (enc : (j : J) → (Fin (b j) → Bool) ↪ A) (F : SAT.CNF V) :
    Factor.count (cnfFactorSystem positions enc F) = SAT.count F := by
  classical
  rw [cnfFactorSystem, factorSystem_count]
  rw [Nat.card_congr (cnfSourceSolutionEquiv positions F)]
  simpa only [Nat.card_eq_fintype_card, SAT.count, SAT.satisfyingAssignments] using
    (Fintype.card_subtype (fun a : SAT.Assignment V => F.eval a = true))

theorem cnfFactorSystem_count_pos_iff {A : Type w} [DecidableEq A] [Fintype A]
    [Fintype V] [Fintype J]
    (positions : V ≃ (j : J) × Fin (b j))
    (enc : (j : J) → (Fin (b j) → Bool) ↪ A) (F : SAT.CNF V) :
    0 < Factor.count (cnfFactorSystem positions enc F) ↔ SAT.Satisfiable F := by
  rw [cnfFactorSystem_count, SAT.count_pos_iff]

omit [DecidableEq V] in
theorem cnfFactorSystem_scope_card_le {A : Type w} [DecidableEq A]
    (positions : V ≃ (j : J) × Fin (b j))
    (enc : (j : J) → (Fin (b j) → Bool) ↪ A) (F : SAT.CNF V)
    {k : ℕ} (hk : 1 ≤ k) (hF : SAT.WidthAtMost k F)
    (e : J ⊕ {C // C ∈ F}) :
    ((cnfFactorSystem positions enc F).scope e).card ≤ k := by
  cases e with
  | inl j => simpa [cnfFactorSystem, factorSystem, factorScope] using hk
  | inr C => exact (cnfScope_card_le positions F C).trans (hF C.val C.property)

omit [DecidableEq V] in
theorem cnfFactorSystem_scope_nonempty {A : Type w} [DecidableEq A]
    (positions : V ≃ (j : J) × Fin (b j))
    (enc : (j : J) → (Fin (b j) → Bool) ↪ A) (F : SAT.CNF V)
    (hF : ∀ C ∈ F, C.Nonempty) (e : J ⊕ {C // C ∈ F}) :
    ((cnfFactorSystem positions enc F).scope e).Nonempty := by
  cases e with
  | inl j => simp [cnfFactorSystem, factorSystem, factorScope]
  | inr C => exact (cnfScope_nonempty_iff positions F C).2 (hF C.val C.property)

/-- The concrete finite-label packing from Section 3. -/
noncomputable def packedCNF {p : ℕ} (positions : V ≃ (j : J) × Fin (b j))
    (capacity : ∀ j, 2 ^ b j ≤ p) (F : SAT.CNF V) :
    Factor.System J (J ⊕ {C // C ∈ F}) (Fin p) :=
  cnfFactorSystem positions (fun j => BooleanPacking.chunkEmbedding (capacity j)) F

theorem packedCNF_count [Fintype V] [Fintype J] {p : ℕ}
    (positions : V ≃ (j : J) × Fin (b j))
    (capacity : ∀ j, 2 ^ b j ≤ p) (F : SAT.CNF V) :
    Factor.count (packedCNF positions capacity F) = SAT.count F :=
  cnfFactorSystem_count positions (fun j => BooleanPacking.chunkEmbedding (capacity j)) F

omit [DecidableEq V] in
/-- The validity table accepts exactly the prescribed initial segment. -/
theorem packedCNF_unary_iff {p : ℕ} (positions : V ≃ (j : J) × Fin (b j))
    (capacity : ∀ j, 2 ^ b j ≤ p) (F : SAT.CNF V) (x : J → Fin p) (j : J) :
    Factor.evalFactor (packedCNF positions capacity F) (.inl j) x = true ↔
      (x j).val < 2 ^ b j := by
  change decide (∃ y, BooleanPacking.chunkEmbedding (capacity j) y = x j) = true ↔ _
  rw [decide_eq_true_eq]
  exact BooleanPacking.mem_range_chunkEmbedding (capacity j) (x j)

/-- The same concrete packing into `ZMod p`; primality is only needed later for
field operations, not for count preservation. -/
noncomputable def primeLabelCNF {p : ℕ} [NeZero p] (positions : V ≃ (j : J) × Fin (b j))
    (capacity : ∀ j, 2 ^ b j ≤ p) (F : SAT.CNF V) :
    Factor.System J (J ⊕ {C // C ∈ F}) (ZMod p) :=
  cnfFactorSystem positions (fun j => BooleanPacking.chunkZModEmbedding (capacity j)) F

theorem primeLabelCNF_count [Fintype V] [Fintype J] {p : ℕ} [NeZero p]
    (positions : V ≃ (j : J) × Fin (b j))
    (capacity : ∀ j, 2 ^ b j ≤ p) (F : SAT.CNF V) :
    Factor.count (primeLabelCNF positions capacity F) = SAT.count F :=
  cnfFactorSystem_count positions (fun j => BooleanPacking.chunkZModEmbedding (capacity j)) F

omit [DecidableEq V] in
theorem primeLabelCNF_unary_iff {p : ℕ} [NeZero p]
    (positions : V ≃ (j : J) × Fin (b j))
    (capacity : ∀ j, 2 ^ b j ≤ p) (F : SAT.CNF V) (x : J → ZMod p) (j : J) :
    Factor.evalFactor (primeLabelCNF positions capacity F) (.inl j) x = true ↔
      (x j).val < 2 ^ b j := by
  change decide (∃ y, BooleanPacking.chunkZModEmbedding (capacity j) y = x j) = true ↔ _
  rw [decide_eq_true_eq]
  exact BooleanPacking.mem_range_chunkZModEmbedding (capacity j) (x j)

end CNF

end SubexponentialSAT.FactorReduction

end OAI.Algorithms
