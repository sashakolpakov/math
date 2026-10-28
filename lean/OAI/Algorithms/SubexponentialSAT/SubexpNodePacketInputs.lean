import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodePacketReady
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPacketCorrectness
import OAI.Algorithms.SubexponentialSAT.SubexpDenseRowTableSemantics

namespace OAI.Algorithms

/-! The physical dense-row traversal and the typed factor packets share
the same factor, incidence, and coordinate order. Origins are constructed
from the actual shifted constant terms, not supplied as a separate table. -/

namespace SubexponentialSAT.SubexpNodePacketInputs

open SubexpSelectedConversions SubexpLiftRing
open SubexpFactorPacketProvenance (Code)
open SubexpTaylorRowCorrectness (RowExpr)

private theorem ofFn_get_map {X Y : Type*} (xs : List X) (f : X → Y) :
    List.ofFn (fun i : Fin xs.length => f (xs.get i)) = xs.map f := by
  change List.ofFn (f ∘ xs.get) = _
  rw [← List.map_ofFn, List.ofFn_get]

private theorem range_map {X : Type*} (D : ℕ) (f : ℕ → X) :
    (List.finRange D).map (fun i => f i.val) = (List.range D).map f := by
  apply List.ext_getElem <;> simp

private theorem ofFn_range {X : Type*} (D : ℕ) (f : ℕ → X) :
    List.ofFn (fun i : Fin D => f i.val) = (List.range D).map f := by
  rw [List.ofFn_eq_map]
  exact range_map D f

private theorem mapIdx_ofFn {X Y : Type*} (xs : List X) (f : ℕ → X → Y) :
    xs.mapIdx f = List.ofFn (fun i : Fin xs.length => f i.val (xs.get i)) := by
  apply List.ext_getElem <;> simp

theorem expressionRows_mapIdx {X : Type*} (expr : ℕ → ℕ → ℕ → X)
    (D start : ℕ) (scopes : List (List ℕ)) :
    SubexpDenseRowTableSemantics.expressionRows expr D start scopes =
      (scopes.mapIdx (fun e scope => scope.map
        (fun v => (List.range D).map (expr (start + e) v)))).flatten := by
  induction scopes generalizing start with
  | nil => rfl
  | cons scope scopes ih =>
      simp only [SubexpDenseRowTableSemantics.expressionRows, List.mapIdx_cons,
        List.flatten_cons, Nat.add_zero, ih]
      congr 2
      apply congrArg (fun f => scopes.mapIdx f)
      funext e scope
      simp only [Nat.add_comm, Nat.add_left_comm]

theorem expressionRows_ofFn {X : Type*} (expr : ℕ → ℕ → ℕ → X)
    (D : ℕ) (scopes : List (List ℕ)) :
    SubexpDenseRowTableSemantics.expressionRows expr D 0 scopes =
      (List.ofFn (fun e : Fin scopes.length => (scopes.get e).map
        (fun v => (List.range D).map (expr e.val v)))).flatten := by
  rw [expressionRows_mapIdx, mapIdx_ofFn]
  simp only [Nat.zero_add]

theorem expressionRows_map {X Y : Type*} (expr : ℕ → ℕ → ℕ → X)
    (f : X → Y) (D start : ℕ) (scopes : List (List ℕ)) :
    (SubexpDenseRowTableSemantics.expressionRows expr D start scopes).map (List.map f) =
      SubexpDenseRowTableSemantics.expressionRows
        (fun e v w => f (expr e v w)) D start scopes := by
  induction scopes generalizing start with
  | nil => rfl
  | cons scope scopes ih =>
      simp only [SubexpDenseRowTableSemantics.expressionRows, List.map_append,
        List.map_map, Function.comp_def, ih]

variable {p D : ℕ} [Fact p.Prime]
variable (source : Prepared p 0) (target : Prepared p D) (theta : Code p D)
variable (R : ℕ) (sourceWidth : List Bool)
variable (hw : sourceWidth.length = baseWidth p 1)
variable (cache : List (List (Code p D))) (zero one : Code p D)

/-- The exact source-width quartet produced by the origin program. -/
def origin (e : RowExpr p) :=
  SubexpOriginCacheSemantics.origin p (D + 1) source target.modulus target.reduction theta
    R (R + 1) (Nat.succ_pos R) source.modulus sourceWidth hw e

/-- A factor is assembled from its actual scope encounter order. Its
origin entries are the computed residues of the shifted constant terms. -/
def factorAt (expr : ℕ → ℕ → ℕ → RowExpr p) (e : ℕ)
    (scope : List ℕ) (answers : List Bool) : SubexpFactorPacketCorrectness.FactorInput p D where
  scope := scope
  degree := R
  data := {
    cache := cache
    rows := SubexpRankedTable.attachAnswers zero one answers
    origins := fun i w => origin source target theta R sourceWidth hw
      (expr e (scope.get i) w.val)
    sourceRows := fun i w => expr e (scope.get i) w.val }
  answers := answers

def factor (expr : ℕ → ℕ → ℕ → RowExpr p) (scopes : List (List ℕ))
    (tables : List (List Bool)) (e : Fin scopes.length) :
    SubexpFactorPacketCorrectness.FactorInput p D :=
  factorAt source target theta R sourceWidth hw cache zero one expr e.val
    (scopes.get e) (tables.getD e.val [])

theorem prefix_origins (expr : ℕ → ℕ → ℕ → RowExpr p) (e : ℕ)
    (scope : List ℕ) (answers : List Bool) :
    (SubexpFactorPacketCorrectness.factorPrefixes source target theta
      (factorAt source target theta R sourceWidth hw cache zero one expr e scope answers)).map
      Subexp.FactorPacketCoordinates.Prefix.origin =
      scope.map (fun v => (List.range D).map (fun w => SubexpFlatLift.encode
        (origin source target theta R sourceWidth hw (expr e v w)))) := by
  simp only [SubexpFactorPacketCorrectness.factorPrefixes,
    SubexpFactorPacketProvenance.prefixes, List.map_ofFn, Function.comp_def,
    SubexpFactorPacketProvenance.coordinatePrefix, factorAt]
  have he (a : SubexpInputBitProgram.ResidueCode p) : SubexpQuarticFlatMul.flat a =
      SubexpFlatLift.encode a := (SubexpOriginCacheSemantics.encode_eq_flat a).symm
  simp only [he]
  rw [← ofFn_get_map scope (fun v => (List.range D).map (fun w => SubexpFlatLift.encode
    (origin source target theta R sourceWidth hw (expr e v w))))]
  apply congrArg List.ofFn
  funext i
  exact range_map D (fun w => SubexpFlatLift.encode
    (origin source target theta R sourceWidth hw (expr e (scope.get i) w)))

theorem prefix_columns (expr : ℕ → ℕ → ℕ → RowExpr p) (e : ℕ)
    (scope : List ℕ) (answers : List Bool) :
    (SubexpFactorPacketCorrectness.factorPrefixes source target theta
      (factorAt source target theta R sourceWidth hw cache zero one expr e scope answers)).map
      Subexp.FactorPacketCoordinates.Prefix.taylor =
      scope.map (fun v => (List.range D).map (fun w =>
        (SubexpTaylorRowCorrectness.column p (D + 1) source target.modulus target.reduction
          theta R (R + 1) (expr e v w)).map SubexpTaylorRow.flat)) := by
  simp only [SubexpFactorPacketCorrectness.factorPrefixes,
    SubexpFactorPacketProvenance.prefixes, List.map_ofFn, Function.comp_def,
    SubexpFactorPacketProvenance.coordinatePrefix, SubexpFactorPacketProvenance.columns,
    SubexpTaylorRowCorrectness.columns, factorAt]
  change List.ofFn (fun i : Fin scope.length => List.ofFn (fun w : Fin D =>
    (SubexpTaylorRowCorrectness.column p (D + 1) source target.modulus target.reduction
      theta R (R + 1) (expr e (scope.get i) w.val)).map SubexpTaylorRow.flat)) = _
  rw [← ofFn_get_map scope (fun v => (List.range D).map (fun w =>
    (SubexpTaylorRowCorrectness.column p (D + 1) source target.modulus target.reduction
      theta R (R + 1) (expr e v w)).map SubexpTaylorRow.flat))]
  apply congrArg List.ofFn
  funext i
  exact ofFn_range D (fun w =>
    (SubexpTaylorRowCorrectness.column p (D + 1) source target.modulus target.reduction
      theta R (R + 1) (expr e (scope.get i) w)).map SubexpTaylorRow.flat)

variable (expr : ℕ → ℕ → ℕ → RowExpr p) (scopes : List (List ℕ))
variable (tables : List (List Bool))

/-- The complete cross-stage input identity. The only list-alignment
premise is one Boolean table per actual scope. No packet, origin, or Taylor
output equality is supplied. -/
theorem inputs_eq_physicalInputs (htables : tables.length = scopes.length) :
    SubexpNodePacketReady.inputs p (D + 1) source target.modulus target.reduction theta
      R (R + 1) (Nat.succ_pos R) sourceWidth hw
      (SubexpDenseRowTableSemantics.expressionRows expr D 0 scopes) scopes tables
      (cache.map (List.map SubexpQuarticFlatNeg.flat))
      (SubexpQuarticFlatNeg.flat zero) (SubexpQuarticFlatNeg.flat one) =
    SubexpFactorPacketCorrectness.physicalInputs source target theta cache
      source.modulus.bits zero one
      ((List.finRange scopes.length).map
        (factor source target theta R sourceWidth hw cache zero one expr scopes tables)) := by
  have horigins :
      ((List.ofFn (fun e : Fin scopes.length =>
        SubexpFactorPacketCorrectness.factorPrefixes source target theta
          (factor source target theta R sourceWidth hw cache zero one expr scopes tables e))).flatten).map
        Subexp.FactorPacketCoordinates.Prefix.origin =
      (SubexpDenseRowTableSemantics.expressionRows expr D 0 scopes).map
        (List.map (fun e => SubexpFlatLift.encode (origin source target theta R sourceWidth hw e))) := by
    rw [List.map_flatten, List.map_ofFn, expressionRows_map, expressionRows_ofFn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext e
    exact prefix_origins source target theta R sourceWidth hw cache zero one expr e.val
      (scopes.get e) (tables.getD e.val [])
  have hcolumns :
      ((List.ofFn (fun e : Fin scopes.length =>
        SubexpFactorPacketCorrectness.factorPrefixes source target theta
          (factor source target theta R sourceWidth hw cache zero one expr scopes tables e))).flatten).map
        Subexp.FactorPacketCoordinates.Prefix.taylor =
      (SubexpDenseRowTableSemantics.expressionRows expr D 0 scopes).map
        (List.map (fun e =>
          (SubexpTaylorRowCorrectness.column p (D + 1) source target.modulus target.reduction
            theta R (R + 1) e).map SubexpTaylorRow.flat)) := by
    rw [List.map_flatten, List.map_ofFn, expressionRows_map, expressionRows_ofFn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext e
    exact prefix_columns source target theta R sourceWidth hw cache zero one expr e.val
      (scopes.get e) (tables.getD e.val [])
  have hscope : List.ofFn (fun e : Fin scopes.length =>
      (factor source target theta R sourceWidth hw cache zero one expr scopes tables e).scope) =
      scopes := List.ofFn_get scopes
  have htable : List.ofFn (fun e : Fin scopes.length =>
      (factor source target theta R sourceWidth hw cache zero one expr scopes tables e).answers) =
      tables := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, htables]
    · intro n hn hm
      simp only [List.getElem_ofFn, factor, factorAt]
      exact List.getD_eq_getElem tables [] hm
  simp only [SubexpNodePacketReady.inputs, SubexpOriginCacheSemantics.origins,
    SubexpFactorPacketCorrectness.physicalInputs, List.map_map, Function.comp_def,
    ← List.ofFn_eq_map]
  congr 1
  · simpa only [List.map_ofFn, Function.comp_def, origin] using horigins.symm
  · simpa only [List.map_ofFn, Function.comp_def] using hcolumns.symm
  · simpa only [List.map_ofFn, Function.comp_def] using hscope.symm
  · simpa only [List.map_ofFn, Function.comp_def] using htable.symm

/-- Packet readiness follows by rewriting the proved cross-stage identity. -/
theorem ready (htables : tables.length = scopes.length) {d : SubexpFactorPacketProgram.Data}
    (h : SubexpFactorPacketProgram.Ready d
      (SubexpNodePacketReady.inputs p (D + 1) source target.modulus target.reduction theta
        R (R + 1) (Nat.succ_pos R) sourceWidth hw
        (SubexpDenseRowTableSemantics.expressionRows expr D 0 scopes) scopes tables
        (cache.map (List.map SubexpQuarticFlatNeg.flat))
        (SubexpQuarticFlatNeg.flat zero) (SubexpQuarticFlatNeg.flat one))) :
    SubexpFactorPacketProgram.Ready d
      (SubexpFactorPacketCorrectness.physicalInputs source target theta cache source.modulus.bits
        zero one ((List.finRange scopes.length).map
          (factor source target theta R sourceWidth hw cache zero one expr scopes tables))) := by
  rw [inputs_eq_physicalInputs source target theta R sourceWidth hw cache zero one
    expr scopes tables htables] at h
  exact h

@[simp] theorem factor_scope (e : Fin scopes.length) :
    (factor source target theta R sourceWidth hw cache zero one expr scopes tables e).scope =
      scopes.get e := rfl

@[simp] theorem factor_cache (e : Fin scopes.length) :
    (factor source target theta R sourceWidth hw cache zero one expr scopes tables e).data.cache =
      cache := rfl

@[simp] theorem factor_answers (e : Fin scopes.length) :
    (factor source target theta R sourceWidth hw cache zero one expr scopes tables e).answers =
      tables.getD e.val [] := rfl

@[simp] theorem factor_rows (e : Fin scopes.length) :
    (factor source target theta R sourceWidth hw cache zero one expr scopes tables e).data.rows =
      SubexpRankedTable.attachAnswers zero one
        (factor source target theta R sourceWidth hw cache zero one expr scopes tables e).answers := rfl

theorem factor_sourceRow (e : Fin scopes.length) (i : Fin (scopes.get e).length) (w : Fin D) :
    (factor source target theta R sourceWidth hw cache zero one expr scopes tables e).data.sourceRows i w =
      expr e.val ((scopes.get e).get i) w.val := rfl

section Computed

variable {r Q Δ : ℕ} (xs : List (ZMod p))
variable (inverse negative : Fin Q → List Bool)
variable (difference : Fin Q → Fin Q → List Bool)
variable (P : Subexp.ConstructivePacking.PackingData (Fin D)
  (MulticolorTypes.UniversalType r Q Δ))
variable (hd : ∀ v : Fin D, Subexp.IncidencePlanSpec.degree scopes v.val ≤ Δ)

/-- The packet factor at the same numeric occurrence used by the actual
complete dense-row producer. -/
def computedFactor (e : Fin scopes.length) : SubexpFactorPacketCorrectness.FactorInput p D :=
  factor source target theta xs.length sourceWidth hw cache zero one
    (SubexpDenseRowTableSemantics.expressionFor source xs inverse negative difference P scopes hd)
    scopes tables e

theorem computed_inputs_eq (htables : tables.length = scopes.length) :
    SubexpNodePacketReady.inputs p (D + 1) source target.modulus target.reduction theta
      xs.length (xs.length + 1) (Nat.succ_pos xs.length) sourceWidth hw
      (SubexpDenseRowTableSemantics.expressions source xs inverse negative difference P scopes hd)
      scopes tables (cache.map (List.map SubexpQuarticFlatNeg.flat))
      (SubexpQuarticFlatNeg.flat zero) (SubexpQuarticFlatNeg.flat one) =
    SubexpFactorPacketCorrectness.physicalInputs source target theta cache source.modulus.bits zero one
      ((List.finRange scopes.length).map
        (computedFactor source target theta sourceWidth hw cache zero one scopes tables
          xs inverse negative difference P hd)) := by
  exact inputs_eq_physicalInputs source target theta xs.length sourceWidth hw cache zero one
    (SubexpDenseRowTableSemantics.expressionFor source xs inverse negative difference P scopes hd)
    scopes tables htables

theorem computed_ready (htables : tables.length = scopes.length)
    {d : SubexpFactorPacketProgram.Data}
    (h : SubexpFactorPacketProgram.Ready d
      (SubexpNodePacketReady.inputs p (D + 1) source target.modulus target.reduction theta
        xs.length (xs.length + 1) (Nat.succ_pos xs.length) sourceWidth hw
        (SubexpDenseRowTableSemantics.expressions source xs inverse negative difference P scopes hd)
        scopes tables (cache.map (List.map SubexpQuarticFlatNeg.flat))
        (SubexpQuarticFlatNeg.flat zero) (SubexpQuarticFlatNeg.flat one))) :
    SubexpFactorPacketProgram.Ready d
      (SubexpFactorPacketCorrectness.physicalInputs source target theta cache source.modulus.bits zero one
        ((List.finRange scopes.length).map
          (computedFactor source target theta sourceWidth hw cache zero one scopes tables
            xs inverse negative difference P hd))) := by
  rw [computed_inputs_eq source target theta sourceWidth hw cache zero one scopes tables
    xs inverse negative difference P hd htables] at h
  exact h

end Computed

end SubexponentialSAT.SubexpNodePacketInputs

end OAI.Algorithms
