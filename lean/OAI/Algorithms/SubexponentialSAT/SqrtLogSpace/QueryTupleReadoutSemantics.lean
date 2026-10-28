import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSelected

/-! Exact readout of the emitted first-occurrence tuples. The equivalences
below preserve the numeric representative at every head. They are proof-level
reindexings of the native traversal, not stored families or evaluator services. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleReadoutSemantics

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog Moments SignatureTupleDFS SignatureTupleTraversal
open Classical

section Representatives

variable {r : ℕ} {count : ℕ → ℕ} {K : ℕ → Type*}
    {X L : Fin r → Type*} [∀ g, Fintype (X g)] [∀ g, DecidableEq (L g)]

/-- Actual full-key equality and source-label equality identify the same
first occurrence. The underlying bounded candidate is unchanged. -/
def tupleLabelEquiv (key : (i : ℕ) → Fin (count i) → K i)
    (enumerate : ∀ g : Fin r, Fin (count g.val) ≃ X g)
    (label : ∀ g, X g → L g)
    (hkernel : ∀ g i j, key g.val i = key g.val j ↔
      label g (enumerate g i) = label g (enumerate g j)) :
    Prefix (Representatives key) r ≃ (∀ g, LabelValue label g) :=
  (Equiv.piCongrRight (fun g : Fin r =>
    representativeKernelEquiv (key g.val) (fun i => label g (enumerate g i))
      (hkernel g))).trans (representativeLabelTupleEquiv enumerate label)

@[simp] theorem tupleLabelEquiv_value (key : (i : ℕ) → Fin (count i) → K i)
    (enumerate : ∀ g : Fin r, Fin (count g.val) ≃ X g)
    (label : ∀ g, X g → L g)
    (hkernel : ∀ g i j, key g.val i = key g.val j ↔
      label g (enumerate g i) = label g (enumerate g j))
    (reps : Prefix (Representatives key) r) (g : Fin r) :
    (tupleLabelEquiv key enumerate label hkernel reps g).val =
      label g (enumerate g (reps g).val) := rfl

/-- The attained-label grouping chooses the same assignments that the actual
first-occurrence traversal emitted; no correction restriction is added. -/
def labelRepresentatives (key : (i : ℕ) → Fin (count i) → K i)
    (enumerate : ∀ g : Fin r, Fin (count g.val) ≃ X g)
    (label : ∀ g, X g → L g)
    (hkernel : ∀ g i j, key g.val i = key g.val j ↔
      label g (enumerate g i) = label g (enumerate g j))
    (y : ∀ g, LabelValue label g) (g : Fin r) : LabelBucket label g (y g) :=
  ⟨enumerate g (((tupleLabelEquiv key enumerate label hkernel).symm y) g).val,
    congrArg (fun z => (z g).val)
      ((tupleLabelEquiv key enumerate label hkernel).apply_symm_apply y)⟩

@[simp] theorem labelRepresentatives_emitted
    (key : (i : ℕ) → Fin (count i) → K i)
    (enumerate : ∀ g : Fin r, Fin (count g.val) ≃ X g)
    (label : ∀ g, X g → L g)
    (hkernel : ∀ g i j, key g.val i = key g.val j ↔
      label g (enumerate g i) = label g (enumerate g j))
    (reps : Prefix (Representatives key) r) (g : Fin r) :
    (labelRepresentatives key enumerate label hkernel
      (tupleLabelEquiv key enumerate label hkernel reps) g).val =
      enumerate g (reps g).val := by
  simp only [labelRepresentatives, Equiv.symm_apply_apply]

/-- Multiplicity one is inherited from the proved first-occurrence
equivalence, with the actual representative assignment in every summand. -/
theorem sum_emitted (key : (i : ℕ) → Fin (count i) → K i)
    (enumerate : ∀ g : Fin r, Fin (count g.val) ≃ X g)
    (label : ∀ g, X g → L g)
    (hkernel : ∀ g i j, key g.val i = key g.val j ↔
      label g (enumerate g i) = label g (enumerate g j))
    {M : Type*} [AddCommMonoid M] (value : (∀ g, X g) → M) :
    (∑ reps : Prefix (Representatives key) r,
      value (fun g => enumerate g (reps g).val)) =
    ∑ y : ∀ g, LabelValue label g,
      value (fun g => (labelRepresentatives key enumerate label hkernel y g).val) := by
  classical
  simpa only [labelRepresentatives_emitted] using
    (tupleLabelEquiv key enumerate label hkernel).sum_comp
      (fun y => value (fun g => (labelRepresentatives key enumerate label hkernel y g).val))

end Representatives

section Readout

variable {r : ℕ} {count : ℕ → ℕ} {K : ℕ → Type*}
    {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R]
    {L : Fin r → Type*} [∀ g, DecidableEq (L g)]

/-- The exact native tuple value: full-head key and correction tests remain
inside each head sum, and additive readout remains outside the full product. -/
theorem emitted_readout (t J : ℕ) (head : V → Fin r)
    (key : (i : ℕ) → Fin (count i) → K i)
    (enumerate : ∀ g : Fin r, Fin (count g.val) ≃ (Head head g → Bool))
    (label : ∀ g, (Head head g → Bool) → L g)
    (hkernel : ∀ g i j, key g.val i = key g.val j ↔
      label g (enumerate g i) = label g (enumerate g j))
    (E : Finset V) (A : Fin r → (V → Bool) → Dense R t J) :
    (∑ reps : Prefix (Representatives key) r,
      Dense.readout (∏ g, ∑ a : Head head g → Bool,
        if label g a = label g (enumerate g (reps g).val) ∧
            (∀ v : Head head g, v.val ∈ E → a v = true) then
          A g (assemble head (Function.update (fun h => enumerate h (reps h).val) g a))
        else 0)) =
    ∑ y : ∀ g, LabelValue label g,
      Dense.readout (∏ g, ∑ a : Head head g → Bool,
        if label g a = (y g).val ∧ (∀ v : Head head g, v.val ∈ E → a v = true) then
          A g (assemble head (Function.update
            (fun h => (labelRepresentatives key enumerate label hkernel y h).val) g a))
        else 0) := by
  classical
  have h := sum_emitted key enumerate label hkernel
    (fun reps => Dense.readout (∏ g, ∑ a : Head head g → Bool,
      if label g a = label g (reps g) ∧ (∀ v : Head head g, v.val ∈ E → a v = true) then
        A g (assemble head (Function.update reps g a)) else 0))
  simpa only [(labelRepresentatives key enumerate label hkernel _ _).property] using h

/-- Reindex the existing finite-difference/grouping theorem by exactly the
tuples emitted by the native traversal. No coefficient identity is reproved. -/
theorem grouped_dense_query_emitted (t J : ℕ) (head : V → Fin r)
    (key : (i : ℕ) → Fin (count i) → K i)
    (enumerate : ∀ g : Fin r, Fin (count g.val) ≃ (Head head g → Bool))
    (label : ∀ g, (Head head g → Bool) → L g)
    (hkernel : ∀ g i j, key g.val i = key g.val j ↔
      label g (enumerate g i) = label g (enumerate g j))
    (A : Fin r → (V → Bool) → Squarefree.Jet V R)
    (hadm : ∀ x, Squarefree.Admissible (∏ g, A g x))
    (hlocal : ∀ (U : Finset V) g x z,
      split head x g = split head z g →
      (∀ h, h ≠ g → label h (split head x h) = label h (split head z h)) →
      QueryEvaluation.specializeDense t J (fun v => decide (v ∈ U)) (A g x) =
        QueryEvaluation.specializeDense t J (fun v => decide (v ∈ U)) (A g z)) :
    Dense.readout (∑ x, QueryEvaluation.specializeDense t J x (∏ g, A g x)) =
      ∑ E ∈ Finset.univ.filter (fun E : Finset V => E.card < J), ∑ U ∈ E.powerset,
        ((-1 : ℤ) ^ (E.card - U.card)) •
          ∑ reps : Prefix (Representatives key) r,
            Dense.readout (∏ g, ∑ a : Head head g → Bool,
              if label g a = label g (enumerate g (reps g).val) ∧
                  (∀ v : Head head g, v.val ∈ E → a v = true) then
                QueryEvaluation.specializeDense t J (fun v => decide (v ∈ U))
                  (A g (assemble head
                    (Function.update (fun h => enumerate h (reps h).val) g a)))
              else 0) := by
  rw [QueryJetSemantics.grouped_dense_query_rescan t J head label
    (labelRepresentatives key enumerate label hkernel) A hadm hlocal]
  apply Finset.sum_congr rfl
  intro E _
  apply Finset.sum_congr rfl
  intro U _
  apply congrArg (fun a => ((-1 : ℤ) ^ (E.card - U.card)) • a)
  exact (emitted_readout t J head key enumerate label hkernel E
    (fun g x => QueryEvaluation.specializeDense t J (fun v => decide (v ∈ U)) (A g x))).symm

/-- For zero levels the actual traversal emits the unique empty tuple and
the empty product contributes the unit exactly once. This needs no head map. -/
theorem zero_head_readout (t J : ℕ)
    (key : (i : ℕ) → Fin (count i) → K i)
    (A : Prefix (Representatives key) 0 → Fin 0 → Dense R t J) :
    (∑ reps : Prefix (Representatives key) 0, Dense.readout (∏ g, A reps g)) =
      Dense.readout (1 : Dense R t J) := by
  classical
  simp

end Readout

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleReadoutSemantics
