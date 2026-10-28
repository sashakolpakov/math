import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainPhysicalSystem
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutTableOrder
import OAI.Algorithms.SubexponentialSAT.SubexpRankedTable

namespace OAI.Algorithms

/-!
# The generated tables belong to the physical numeric factor system

The ambient dimension is transported using the proved chunk-count equality.
The factor and scope orders remain the emitted orders. This file identifies
the Boolean table payloads and their attached descending labels; it assumes
neither a prepared packet nor a desired table-polynomial equality.
-/

noncomputable section

namespace SubexponentialSAT.SubexpMainPhysicalTables

open Subexp.ConstructivePacking Subexp.OrderedScopeSystem
open SubexpLeafTables SubexpTableInterpolation

private theorem ofFn_factorEquiv {D : ℕ} {F B : Type*} [DecidableEq F]
    (factors : FiniteEnumeration F) (scopes : F → List (Fin D)) (f : F → B) :
    List.ofFn (fun i => f (factorEquiv factors scopes i)) = factors.values.map f := by
  calc
    _ = List.ofFn (fun i : Fin factors.values.length => f (factors.values.get i)) := by
      have h := List.ofFn_congr (rawScopes_length factors scopes)
        (fun i => f (factorEquiv factors scopes i))
      exact h
    _ = _ := by
      change List.ofFn (f ∘ factors.values.get) = _
      rw [← List.map_ofFn, List.ofFn_get]

private theorem table_cast {D p m n : ℕ} [Fact p.Prime] {F : Type*}
    (S : Factor.System (Fin D) F (ZMod p)) (e : F)
    (index : Fin m ≃ {v // v ∈ S.scope e}) (h : n = m) :
    (orderedRows S e ((finCongr h).trans index) false true).map Row.value =
      (orderedRows S e index false true).map Row.value := by
  cases h
  rfl

private theorem attach_table {D p m : ℕ} [Fact p.Prime] {F C : Type*}
    (S : Factor.System (Fin D) F (ZMod p)) (e : F)
    (index : Fin m ≃ {v // v ∈ S.scope e}) (zero one : C) :
    SubexpRankedTable.attachAnswers zero one
      ((orderedRows S e index false true).map Row.value) = orderedRows S e index zero one := by
  have hb : ∀ b : Bool, (if b = true then true else false) = b := by
    intro b
    cases b <;> rfl
  have hvalues : (orderedRows S e index false true).map Row.value =
      (SubexpDigitGrid.descending p m).map
        (fun a => S.table e (fun v => ZMod.finEquiv p (a.get (index.symm v)))) := by
    simp only [orderedRows, SubexpDigitGrid.rows, List.map_map, Function.comp_def, hb]
  rw [hvalues]
  exact SubexpRankedTable.attachAnswers_map zero one _

variable {n ell D p : ℕ} [Fact p.Prime]
variable (G : SubexpLeafData.Leaf n) (hG : (G.map ExecCNF.clauseSet).Nodup)
variable (hell : 0 < ell) (hcap : 2 ^ ell ≤ p) (hD : D = ChunkPartition.count n ell)

/-- The factor ID is its position in the original unary-then-clause stream. -/
def originalFactor (e : Fin (SubexpLeafScopeOrder.rawScopes G hG hell).length) :=
  factorEquiv (SubexpLeafData.factors G hG)
    (SubexpLeafData.scopes G hG (ChunkPartition.indexEquiv n ell hell)) e

/-- Transport the actual encounter-order scope, not a sorted substitute. -/
def scope (e : Fin (SubexpLeafScopeOrder.rawScopes G hG hell).length) : List (Fin D) :=
  hD.symm ▸ SubexpLeafData.scopes G hG (ChunkPartition.indexEquiv n ell hell)
    (originalFactor G hG hell e)

theorem scope_values (e : Fin (SubexpLeafScopeOrder.rawScopes G hG hell).length) :
    (scope G hG hell hD e).map Fin.val = (SubexpLeafScopeOrder.rawScopes G hG hell).get e := by
  cases hD
  exact (rawScopes_get (SubexpLeafData.factors G hG)
    (SubexpLeafData.scopes G hG (ChunkPartition.indexEquiv n ell hell)) e).symm

theorem scope_length (e : Fin (SubexpLeafScopeOrder.rawScopes G hG hell).length) :
    (scope G hG hell hD e).length =
      ((SubexpLeafScopeOrder.rawScopes G hG hell).get e).length := by
  simpa only [List.length_map] using congrArg List.length (scope_values G hG hell hD e)

theorem scope_nodup (e : Fin (SubexpLeafScopeOrder.rawScopes G hG hell).length) :
    (scope G hG hell hD e).Nodup := by
  cases hD
  exact SubexpLeafData.scopes_nodup G hG (ChunkPartition.indexEquiv n ell hell) _

theorem scope_mem (e : Fin (SubexpLeafScopeOrder.rawScopes G hG hell).length) (v : Fin D) :
    v ∈ scope G hG hell hD e ↔ v ∈ (SubexpMainPhysicalSystem.system G hG hell hcap hD).scope e := by
  cases hD
  exact scopeLists_mem
    (SubexpLEFactorSystem.packed hell hcap (ExecCNF.formulaSet G))
    (SubexpLeafData.factors G hG)
    (SubexpLeafData.scopes G hG (ChunkPartition.indexEquiv n ell hell))
    (SubexpLeafData.scopes_mem G hG (ChunkPartition.indexEquiv n ell hell)
      (PackedSAT.capacity (n := n) hcap)) e v

/-- This index has the raw scope's literal length, as used by the packet
producer, and the transported factor system's exact incidence subtype. -/
def scopeIndex (e : Fin (SubexpLeafScopeOrder.rawScopes G hG hell).length) :
    Fin ((SubexpLeafScopeOrder.rawScopes G hG hell).get e).length ≃
      {v // v ∈ (SubexpMainPhysicalSystem.system G hG hell hcap hD).scope e} :=
  (finCongr (scope_length G hG hell hD e).symm).trans
    (scopeOfList (SubexpMainPhysicalSystem.system G hG hell hcap hD) e
      (scope G hG hell hD e) (scope_nodup G hG hell hD e) (scope_mem G hG hell hcap hD e))

theorem scopeIndex_value (e : Fin (SubexpLeafScopeOrder.rawScopes G hG hell).length)
    (i : Fin ((SubexpLeafScopeOrder.rawScopes G hG hell).get e).length) :
    ((scopeIndex G hG hell hcap hD e i).val).val =
      ((SubexpLeafScopeOrder.rawScopes G hG hell).get e).get i := by
  have hi : i.val < (scope G hG hell hD e).length := by
    rw [scope_length G hG hell hD e]
    exact i.isLt
  have h := congrArg (fun xs : List ℕ => xs[i.val]?) (scope_values G hG hell hD e)
  rw [List.getElem?_map, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem i.isLt] at h
  change ((scope G hG hell hD e).get ⟨i.val, hi⟩).val = _
  simpa only [List.get_eq_getElem] using Option.some.inj h

def table (e : Fin (SubexpLeafScopeOrder.rawScopes G hG hell).length) : List Bool :=
  (orderedRows (SubexpMainPhysicalSystem.system G hG hell hcap hD) e
    (scopeIndex G hG hell hcap hD e) false true).map Row.value

theorem table_eq_factorTable (e : Fin (SubexpLeafScopeOrder.rawScopes G hG hell).length) :
    table G hG hell hcap hD e =
      SubexpLeafTableOrder.factorTable G hG hell hcap (originalFactor G hG hell e) := by
  unfold table scopeIndex
  rw [table_cast]
  cases hD
  rfl

/-- The whole list retains the physical numeric factor order. -/
theorem orderedTables_eq :
    SubexpLeafTableOrder.orderedTables G hG hell hcap =
      List.ofFn (table G hG hell hcap hD) := by
  symm
  calc
    _ = List.ofFn (fun e => SubexpLeafTableOrder.factorTable G hG hell hcap
        (originalFactor G hG hell e)) := by
      apply congrArg List.ofFn
      funext e
      exact table_eq_factorTable G hG hell hcap hD e
    _ = _ := ofFn_factorEquiv (SubexpLeafData.factors G hG)
      (SubexpLeafData.scopes G hG (ChunkPartition.indexEquiv n ell hell))
      (SubexpLeafTableOrder.factorTable G hG hell hcap)

theorem orderedTables_getD (e : Fin (SubexpLeafScopeOrder.rawScopes G hG hell).length) :
    (SubexpLeafTableOrder.orderedTables G hG hell hcap).getD e.val [] = table G hG hell hcap hD e := by
  rw [orderedTables_eq G hG hell hcap hD]
  simp

theorem table_length (e : Fin (SubexpLeafScopeOrder.rawScopes G hG hell).length) :
    (table G hG hell hcap hD e).length =
      p ^ ((SubexpLeafScopeOrder.rawScopes G hG hell).get e).length := by
  simp only [table, List.length_map, orderedRows, SubexpDigitGrid.rows_length]

theorem attachedRows {C : Type*} (zero one : C)
    (e : Fin (SubexpLeafScopeOrder.rawScopes G hG hell).length) :
    SubexpRankedTable.attachAnswers zero one
      ((SubexpLeafTableOrder.orderedTables G hG hell hcap).getD e.val []) =
      orderedRows (SubexpMainPhysicalSystem.system G hG hell hcap hD) e
        (scopeIndex G hG hell hcap hD e) zero one := by
  rw [orderedTables_getD G hG hell hcap hD]
  exact attach_table _ _ _ zero one

section Produced

variable (x : SubexpLayoutConstruction.Inputs)
variable (hv : SubexpClauseFamilyProgram.Valid (SubexpLayoutConstruction.familyInputs x)
  (SubexpLayoutConstruction.dimension x) (SubexpLayoutConstruction.variableCount x))
variable (leaf : SubexpLeafData.Leaf (SubexpLayoutConstruction.variableCount x))
variable (hleaf : (leaf.map ExecCNF.clauseSet).Nodup)
variable (hell' : 0 < CounterPrograms.value x.counts.ell)
variable (hD' : SubexpLayoutConstruction.dimension x =
  ChunkPartition.count (SubexpLayoutConstruction.variableCount x) (CounterPrograms.value x.counts.ell))
variable (hp : BinaryArithmetic.toNat x.counts.modulus = p)
variable (hcap' : 2 ^ CounterPrograms.value x.counts.ell ≤ p)

include hp in
theorem produced_table_getD
    (e : Fin (SubexpLeafScopeOrder.rawScopes leaf hleaf hell').length) :
    (SubexpLayoutConstruction.tables x hv leaf).getD e.val [] =
      table leaf hleaf hell' hcap' hD' e := by
  rw [SubexpLayoutTableOrder.table_payloads_eq x hv leaf hleaf hell' hD' hp hcap']
  exact orderedTables_getD leaf hleaf hell' hcap' hD' e

include hp in
/-- Attaching the physical descending labels to the actual generated
answers gives the exact table of the dimension-transported numeric system. -/
theorem produced_attachedRows {C : Type*} (zero one : C)
    (e : Fin (SubexpLeafScopeOrder.rawScopes leaf hleaf hell').length) :
    SubexpRankedTable.attachAnswers zero one
      ((SubexpLayoutConstruction.tables x hv leaf).getD e.val []) =
      orderedRows (SubexpMainPhysicalSystem.system leaf hleaf hell' hcap' hD') e
        (scopeIndex leaf hleaf hell' hcap' hD' e) zero one := by
  rw [produced_table_getD x hv leaf hleaf hell' hD' hp hcap']
  exact attach_table _ _ _ zero one

end Produced

end SubexponentialSAT.SubexpMainPhysicalTables

end

end OAI.Algorithms
