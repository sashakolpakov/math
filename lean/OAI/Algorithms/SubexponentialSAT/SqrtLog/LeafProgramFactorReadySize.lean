import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorReadyCore

namespace OAI.Algorithms

/-! Explicit parser, accumulator, factor-ID and fetched-payload capacities. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorReady
open SubexponentialSAT BitProgram StructuredCalls MomentsProgram SubexpSetupStorage
open IdempotentApplyProgram.Bounds PerturbationAssembly
attribute [local simp] Fin.coe_ofNat_eq_mod

def payloadBound (rows clauses : List (List Bool)) : ℕ :=
  (rows.map List.length).sum+(clauses.map List.length).sum

theorem getD_length_le (xs : List (List Bool)) (i : ℕ) :
    (xs.getD i []).length ≤ (xs.map List.length).sum := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i =>
      simpa only [List.getD_cons_succ,List.map_cons,List.sum_cons] using
        (ih i).trans (Nat.le_add_left _ _)

theorem selected_length_le (rows clauses : List (List Bool))
    (marked : Bool) (mark f : ℕ) :
    (LeafFactorDispatchProgram.selectedPayload rows clauses marked mark f).length ≤
      payloadBound rows clauses := by
  unfold LeafFactorDispatchProgram.selectedPayload payloadBound
  split
  · exact (getD_length_le rows f).trans (Nat.le_add_right _ _)
  · split
    · exact (getD_length_le clauses mark).trans (Nat.le_add_left _ _)
    · simp

def seedBound (n B d u J : ℕ) : ℕ :=
  byteCapacity n B d u J (capacity (Finset.univ : Finset (Fin n)) u J)

def wordBound (A T C F L : ℕ) : ℕ := A+T+C+F+L+1

theorem worker_bound {n B d : ℕ} (base : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (seed : FactorLoop.Raw n B d) (tail : List Bool) (f : ℕ) (payload : List Bool)
    (u J A T F L : ℕ) (hb : ∀ i,(base i).length ≤ A)
    (hg : Good Finset.univ u J seed) (ht : tail.length ≤ T)
    (hf : f ≤ F) (hp : payload.length ≤ L) :
    WordBound (wordBound A T (seedBound n B d u J) F L)
      (workerState base regs seed tail f payload) := by
  have hs : (Product.bytes seed).length ≤ seedBound n B d u J := bytes_le_capacity _ _ _ _ hg
  intro i
  by_cases h149 : i=149
  · subst i
    simp [workerState,projectState,FactorID.output,payloadState,FactorLoop.state,Encoding.encodeNat]
    unfold wordBound; omega
  by_cases h150 : i=150
  · subst i
    simpa [workerState,projectState,FactorID.output,payloadState,FactorLoop.state,wordBound]
      using (show tail.length ≤ wordBound A T (seedBound n B d u J) F L by unfold wordBound; omega)
  by_cases h151 : i=151
  · subst i
    simpa [workerState,projectState,FactorID.output,payloadState,FactorLoop.state]
      using (show (Product.bytes seed).length ≤ wordBound A T (seedBound n B d u J) F L by unfold wordBound; omega)
  by_cases h154 : i=154
  · subst i
    simpa [workerState,projectState,FactorID.output,payloadState]
      using (show payload.length ≤ wordBound A T (seedBound n B d u J) F L by unfold wordBound; omega)
  by_cases h556 : i=556
  · subst i
    rw [worker_factor,List.length_replicate]
    unfold wordBound; omega
  rw [worker_agree base regs seed tail f payload i (by simp [changes,h149,h150,h151,h154,h556])]
  have := hb i
  unfold wordBound; omega

theorem staged_bound {n B d : ℕ} (base : Fin 768 → List Bool) (regs : Fin 40 → Bool)
    (seed : FactorLoop.Raw n B d) (tail : List Bool) (f : ℕ) (payload : List Bool)
    (u J A T F L : ℕ)
    (hb : ∀ i,(base i).length ≤ A)
    (hb' : WordBound A (Incidence.staged ⟨fun _=>false,base⟩))
    (hg : Good Finset.univ u J seed) (ht : tail.length ≤ T)
    (hf : f ≤ F) (hp : payload.length ≤ L) :
    WordBound (wordBound A T (seedBound n B d u J) F L)
      (Incidence.staged (workerState base regs seed tail f payload)) := by
  have hw := worker_bound base regs seed tail f payload u J A T F L hb hg ht hf hp
  have ha := staged_agree (workerState base regs seed tail f payload)
    ⟨fun _=>false,base⟩ (worker_agree base regs seed tail f payload)
  intro i
  by_cases hi : i ∈ changes
  · rw [staged_changed _ i hi]; exact hw i
  · rw [ha i hi]
    have := hb' i
    unfold wordBound; omega

end SubexponentialSAT.SqrtLog.LeafProgram.FactorReady

end OAI.Algorithms
