import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySourceTarget
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeySource
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSourceAlignment

/-! The exact completed native tuple aggregate, with the same bounded numeric
representatives and the same physical factor IDs, has the source-target value. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget
open scoped BigOperators
open Classical Polynomial OAI OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafProgram NodeConcrete Moments
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleSource
open SignatureTupleRun HeadSourceLocality BucketTupleProgram.Concrete

variable (s : ProducedSource) {d : ℕ}
    (q : Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)

/-- The physical selected-coordinate stream for one produced head. -/
def selectedIds (g : Fin s.input.r) : List ℕ :=
  LeafHeadSetupProgram.selectedHeads s.input.n s.input.rows s.input.low (s.base+g.val)

theorem selectedIds_bound (g : Fin s.input.r) :
    ∀ v ∈ selectedIds s g, v < s.input.n :=
  HeadIdentifierProgram.chosenIds_bound _ _

theorem selectedIds_nodup (g : Fin s.input.r) : (selectedIds s g).Nodup :=
  HeadIdentifierProgram.chosenIds_nodup _ _

/-- The canonical physical order identifies selected bits with typed free-head
assignments. Keeping this equivalence named avoids reconstructing its dependent
proof arguments when it is used in both directions. -/
def selectedEquiv (g : Fin s.input.r) :
    (Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g → Bool) ≃
      (Fin (selectedIds s g).length → Bool) :=
  BucketTupleProgram.Concrete.freeAssignmentEquiv H
    (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g
    (selectedIds s g) (selectedIds_bound s g) (selectedIds_nodup s g)
    (facts.selected g)

/-- Decode the controller's actual bounded numeric candidates in the actual
increasing selected-coordinate order, without choosing new representatives. -/
def enumerate (g : Fin s.input.r) : Fin (2^s.headSize g.val) ≃
    (Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g → Bool) :=
  (AttainedSignatures.assignmentEquiv (s.headSize g.val)).trans
    (selectedEquiv s q H owner head facts g).symm

/-- Every original integer row agrees with the actual source label after only
the proved row-count cast. -/
theorem ordered_key (g : Fin s.input.r) (i : Fin (2^s.headSize g.val)) :
    (fun j : Fin s.input.D =>
      freeLabel q.p q.ps q.packing owner head H s.input.node g
        (enumerate s q H owner head facts g i) (Fin.cast facts.dimension.symm j)) =
      s.key g.val i := by
  have he := SignatureKeySource.ordered_signature q.p q.ps q.packing owner head H
    s.input.node g
    (selectedIds s g) (selectedIds_bound s g) (selectedIds_nodup s g)
    (facts.selected g) (enumerate s q H owner head facts g i)
  have henum : selectedEquiv s q H owner head facts g
      (enumerate s q H owner head facts g i) =
      AttainedSignatures.assignmentEquiv (s.headSize g.val) i := by
    change selectedEquiv s q H owner head facts g
      ((selectedEquiv s q H owner head facts g).symm
        (AttainedSignatures.assignmentEquiv (s.headSize g.val) i)) = _
    exact Equiv.apply_symm_apply _ _
  funext j
  calc
    _ = _ := (congrFun he (Fin.cast facts.dimension.symm j)).symm
    _ = _ := by
      change LayoutSignatureBound.boolSignature _
        (selectedEquiv s q H owner head facts g
          (enumerate s q H owner head facts g i)) _ = _
      rw [henum]
      unfold LayoutSignatureBound.boolSignature LayoutExactBuckets.signature
        ProducedSource.key SignatureTupleLoader.integerMatrix AttainedSignatures.integerKey
      apply Finset.sum_congr rfl
      intro v _
      dsimp only [Fin.val_cast]
      rw [facts.literal]
      rfl

theorem key_kernel (g : Fin s.input.r) (i j : Fin (2^s.headSize g.val)) :
    s.key g.val i = s.key g.val j ↔
      freeLabel q.p q.ps q.packing owner head H s.input.node g
        (enumerate s q H owner head facts g i) =
      freeLabel q.p q.ps q.packing owner head H s.input.node g
        (enumerate s q H owner head facts g j) := by
  rw [← ordered_key s q H owner head facts g i,
    ← ordered_key s q H owner head facts g j]
  exact SignatureTupleSourceAlignment.row_cast_eq_iff facts.dimension.symm _ _

@[simp] theorem emittedRepresentatives_eq
    (ancestors : Prefix (Representatives s.key) s.input.r) :
    emittedRepresentatives s q H owner head facts ancestors =
      fun g => enumerate s q H owner head facts g (ancestors g).val := rfl

private theorem mem_free_image (E : Finset (ResidualEmbedding.Free H))
    (v : ResidualEmbedding.Free H) :
    v.val ∈ E.image Subtype.val ↔ v ∈ E :=
  Subtype.val_injective.mem_finset_image

/-- The completed aggregate is precisely the pure emitted-tuple expression.
The ambient E/U images are the same physical masks, and all factor IDs remain. -/
theorem tuple_total_eq (E U : Finset (ResidualEmbedding.Free H))
    (ids : List ℕ) (color : ℕ → Fin s.input.r)
    (hids : ∀ g : Fin s.input.r, QueryVisitorHead.factorIds s.input g = ids.filter (fun f => color f = g)) :
    tupleTotal s.key s.input.r
      (emittedValue s q H (E.image Subtype.val) (U.image Subtype.val) high owner head facts) =
    tupleTotal s.key s.input.r (fun reps =>
      Dense.readout (∏ g,
        ∑ x : Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g → Bool,
          if freeLabel q.p q.ps q.packing owner head H s.input.node g x =
              freeLabel q.p q.ps q.packing owner head H s.input.node g
                (enumerate s q H owner head facts g (reps g).val) ∧
              (∀ v : Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g,
                v.val ∈ E → x v = true) then
            QueryEvaluation.specializeDense q.p.t q.J (fun v => decide (v ∈ U))
              (sourceProduct q H high
                (stateFor H high (assemble
                  (fun v : ResidualEmbedding.Free H => head s.input.node v.val)
                  (Function.update (fun h => enumerate s q H owner head facts h (reps h).val) g x)))
                (ids.filter (fun f => color f = g)))
          else 0)) := by
  apply congrArg (tupleTotal s.key s.input.r)
  funext reps
  unfold emittedValue
  apply congrArg Dense.readout
  apply Finset.prod_congr rfl
  intro g _
  unfold QueryVisitorHead.headValue QueryVisitorHead.fiberValue
  rw [hids g, emittedRepresentatives_eq]
  have hU : (fun v : ResidualEmbedding.Free H => decide (v.val ∈ U.image Subtype.val)) =
      fun v => decide (v ∈ U) := by
    funext v
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using mem_free_image s H U v
  rw [hU]
  apply Finset.sum_congr rfl
  intro x _
  have hE : (∀ v : Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g,
      v.val.val ∈ E.image Subtype.val → x v = true) ↔
      (∀ v : Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g,
        v.val ∈ E → x v = true) :=
    forall_congr' (fun v => imp_congr (mem_free_image s H E v.val) Iff.rfl)
  exact if_congr (and_congr Iff.rfl hE) rfl rfl

/-- The actual native aggregate, signed by ring multiplication as in the
pair commit, gives every retained coefficient of the shifted source target. -/
theorem signed_target (hu : q.u = q.p.t)
    (howner : ∀ i, (q.ps.get i).1 = (owner i).val)
    (hhead : ∀ i t, (q.packing.label i).head t = head t (owner i))
    (htheta : q.p.ops.decode q.theta = q.p.model.node q.p.t s.input.Q q.p.ht q.p.hfield s.input.node)
    (ids : List ℕ) (hn : ids.Nodup)
    (hh : ∀ id < (AssignmentConcrete.weightedHashes q).length, id ∈ ids)
    (hm : q.marked = true → (AssignmentConcrete.weightedHashes q).length ∈ ids)
    (color : ℕ → Fin s.input.r)
    (hids : ∀ g : Fin s.input.r, QueryVisitorHead.factorIds s.input g = ids.filter (fun f => color f = g))
    (hslot : ∀ f ∈ ids, ∀ j (hj : (j, s.input.n + f) ∈ q.ps),
      (q.packing.label (planIndex q.ps s.input.n f j hj)).slot 0 s.input.node = color f)
    (hhash : ∀ id ∈ ids, ∀ hi : id < (AssignmentConcrete.weightedHashes q).length,
      ∀ w ∈ (AssignmentConcrete.weightedHashes q)[id], ∀ l ∈ w.literals,
        l.variable ∉ H → (l.variable.val, s.input.n + id) ∈ q.ps)
    (hmark : q.marked = true → (AssignmentConcrete.weightedHashes q).length ∈ ids →
      ∀ l ∈ q.markedClause, l.variable ∉ H →
        (l.variable.val, s.input.n + (AssignmentConcrete.weightedHashes q).length) ∈ q.ps)
 :
    (∑ E ∈ Finset.univ.filter (fun E : Finset (ResidualEmbedding.Free H) => E.card < q.J),
      ∑ U ∈ E.powerset, (-1) ^ (E.card - U.card) *
        tupleTotal s.key s.input.r
          (emittedValue s q H (E.image Subtype.val) (U.image Subtype.val) high owner head facts)) =
      Truncated.ofPolynomial q.J ((specTarget q H high).comp
        (X + C (q.p.ops.decode q.theta))) := by
  rw [← QuerySourceTarget.signed_source_target q hu H high owner howner head hhead
    s.input.node htheta ids hn hh hm color hslot facts.source_zero hhash hmark
    s.key (enumerate s q H owner head facts) (key_kernel s q H owner head facts)]
  apply Finset.sum_congr rfl
  intro E _
  apply Finset.sum_congr rfl
  intro U _
  rw [tuple_total_eq s q H high owner head facts E U ids color hids]
  simp only [tupleTotal, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget
