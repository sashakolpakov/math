import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpProgramTables
import OAI.Algorithms.SubexponentialSAT.SubexpSelectedConversions
import OAI.Algorithms.SubexponentialSAT.SubexpTableExecution
import OAI.Algorithms.SubexponentialSAT.SubexpRepresentedBuilder
import OAI.Algorithms.SubexponentialSAT.PackedSAT
import OAI.Algorithms.SubexponentialSAT.SubexpDigitGrid
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking

namespace OAI.Algorithms

/-!
# Concrete finite tables for packed leaf factors

The table producer queries the actual local Boolean factor predicate, once
for each row of its local alphabet. No global assignment or count occurs in
the producer. Coefficients are the prepared zero and one code words.
-/

namespace SubexponentialSAT.SubexpLeafTables

open SubexpSymbolicCost SubexpTableInterpolation

variable {D p : ℕ} [Fact p.Prime] {F C : Type*}

/-- The scope order is computed by sorting the finite set of chunk indices. -/
def scopeEquiv (S : Factor.System (Fin D) F (ZMod p)) (e : F) :
    Fin (S.scope e).card ≃ {v // v ∈ S.scope e} :=
  ((S.scope e).orderIsoOfFin rfl).toEquiv

/-- Enumerate all local rows, retaining zero-valued rows as explicit data. -/
def rows (S : Factor.System (Fin D) F (ZMod p)) (e : F)
    (zero one : C) : List (Row p (S.scope e).card C) :=
  fullRows fun a =>
    if S.table e (fun v => ZMod.finEquiv p (a.get ((scopeEquiv S e).symm v))) = true
    then one else zero

@[simp] theorem rows_length (S : Factor.System (Fin D) F (ZMod p)) (e : F)
    (zero one : C) : (rows S e zero one).length = p ^ (S.scope e).card :=
  fullRows_length _

variable (ops : RepresentedRing C (SubexpActualRing.Ring p (D + 1)))

theorem rows_decode (S : Factor.System (Fin D) F (ZMod p)) (e : F) :
    (rows S e ops.zeroRun.1 ops.oneRun.1).map (SubexpRepresentedBuilder.mapRow ops.decode) =
      fullRows (fun a =>
        if S.table e (fun v => ZMod.finEquiv p (a.get ((scopeEquiv S e).symm v))) = true
        then (1 : SubexpActualRing.Ring p (D + 1)) else 0) := by
  simp only [rows, fullRows, List.map_map, Function.comp_def,
    SubexpRepresentedBuilder.mapRow]
  congr 1
  funext a
  split_ifs <;> simp only [ops.one_correct, ops.zero_correct]

noncomputable def labels : Fin p → SubexpActualRing.Ring p (D + 1) :=
  fun i => ops.decode ((SubexpTableExecution.labelsProgram ops.program p).1.get i)

theorem labelUnits : TableInterpolation.UnitDifferences (labels ops) :=
  SubexpTableExecution.encodedIntegerUnits ops (D + 1) (Fact.out : p.Prime)
    (LiftRing.of (SubexpActualRing.F p (D + 1))) _
    (SubexpTableExecution.labelsProgram_correct ops p)

theorem labels_eq : labels ops = fun i =>
    SubexpActualRing.coordinateLift p (D + 1) (ZMod.finEquiv p i) := by
  funext i
  rw [labels, SubexpTableExecution.labelsProgram_correct]
  simp only [SubexpActualRing.coordinateLift, BooleanPacking.finEquiv_val]

/-- The produced code rows are exactly the interpolated actual factor table,
with the canonical scope order and generated integer-label cache. -/
theorem rows_correct (S : Factor.System (Fin D) F (ZMod p)) (e : F) :
    tablePolynomial (labels ops) (labelUnits ops)
      ((rows S e ops.zeroRun.1 ops.oneRun.1).map
        (SubexpRepresentedBuilder.mapRow ops.decode)) =
      MvPolynomial.rename (scopeEquiv S e).symm
        (GlobalPolynomial.interpolatedTable S (SubexpActualRing.coordinateLift p (D + 1))
          (SubexpActualRing.coordinateLift_unitDifferences p (D + 1)) e) := by
  rw [rows_decode]
  have h := SubexpProgramCorrectness.fullRows_eq_interpolatedTable
    S e (scopeEquiv S e) (ZMod.finEquiv p).toEquiv
    (SubexpActualRing.coordinateLift p (D + 1))
    (SubexpActualRing.coordinateLift_unitDifferences p (D + 1))
  simpa only [labels_eq ops, RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
    EquivLike.coe_coe] using h

/-- The actual emitted scope order is retained, with no sorting step. -/
def scopeOfList (S : Factor.System (Fin D) F (ZMod p)) (e : F)
    (xs : List (Fin D)) (hnodup : xs.Nodup)
    (hmem : ∀ v, v ∈ xs ↔ v ∈ S.scope e) : Fin xs.length ≃ {v // v ∈ S.scope e} :=
  Subexp.ConstructivePacking.listSubtypeEquiv xs hnodup (fun v => v ∈ S.scope e) hmem

/-- Values and labels use the physical descending, first-digit-fastest rank
order. The scope equivalence may be the actual encounter-order list. -/
def orderedRows {m : ℕ} (S : Factor.System (Fin D) F (ZMod p)) (e : F)
    (scope : Fin m ≃ {v // v ∈ S.scope e}) (zero one : C) : List (Row p m C) :=
  SubexpDigitGrid.rows fun a =>
    if S.table e (fun v => ZMod.finEquiv p (a.get (scope.symm v))) = true then one else zero

theorem orderedRows_decode {m : ℕ} (S : Factor.System (Fin D) F (ZMod p)) (e : F)
    (scope : Fin m ≃ {v // v ∈ S.scope e}) :
    (orderedRows S e scope ops.zeroRun.1 ops.oneRun.1).map
      (SubexpRepresentedBuilder.mapRow ops.decode) =
      SubexpDigitGrid.rows (fun a =>
        if S.table e (fun v => ZMod.finEquiv p (a.get (scope.symm v))) = true
        then (1 : SubexpActualRing.Ring p (D + 1)) else 0) := by
  simp only [orderedRows, SubexpDigitGrid.rows, List.map_map, Function.comp_def,
    SubexpRepresentedBuilder.mapRow]
  congr 1
  funext a
  split_ifs <;> simp only [ops.one_correct, ops.zero_correct]

/-- The physical row order gives the same interpolation polynomial, with
coordinates following the actual scope list rather than a sorted substitute. -/
theorem orderedRows_correct {m : ℕ} (S : Factor.System (Fin D) F (ZMod p)) (e : F)
    (scope : Fin m ≃ {v // v ∈ S.scope e}) :
    tablePolynomial (labels ops) (labelUnits ops)
      ((orderedRows S e scope ops.zeroRun.1 ops.oneRun.1).map
        (SubexpRepresentedBuilder.mapRow ops.decode)) =
      MvPolynomial.rename scope.symm
        (GlobalPolynomial.interpolatedTable S (SubexpActualRing.coordinateLift p (D + 1))
          (SubexpActualRing.coordinateLift_unitDifferences p (D + 1)) e) := by
  rw [orderedRows_decode, SubexpDigitGrid.tablePolynomial_rows]
  have h := SubexpProgramCorrectness.fullRows_eq_interpolatedTable
    S e scope (ZMod.finEquiv p).toEquiv
    (SubexpActualRing.coordinateLift p (D + 1))
    (SubexpActualRing.coordinateLift_unitDifferences p (D + 1))
  simpa only [labels_eq ops, RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
    EquivLike.coe_coe] using h

end SubexponentialSAT.SubexpLeafTables

end OAI.Algorithms
