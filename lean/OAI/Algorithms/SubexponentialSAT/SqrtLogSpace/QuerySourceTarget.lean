import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleReadoutSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryJetSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality

/-! The actual colored source products determine the interpolation target.
This joins the emitted first-occurrence sum to the existing source diagonal
identity. Native traversal, serialization and resources remain caller proofs. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySourceTarget

open scoped BigOperators
open Classical Polynomial OAI OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafProgram NodeConcrete Moments
open SignatureTupleDFS SignatureTupleTraversal HeadSourceLocality

variable {r Q n d : ℕ} {count : ℕ → ℕ} {K : ℕ → Type*}

/-- The signed finite-difference sum of the exact emitted tuple values is
the retained shifted source target. Admissibility and full-key locality are
derived from the actual source, rather than assumed as evaluator services. -/
theorem signed_source_target (q : Factor.Spec r Q n d) (hu : q.u = q.p.t)
    (H : Finset (Fin n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin n)
    (howner : ∀ i, (q.ps.get i).1 = (owner i).val)
    (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t, (q.packing.label i).head t = head t (owner i))
    (node : Fin Q)
    (htheta : q.p.ops.decode q.theta = q.p.model.node q.p.t Q q.p.ht q.p.hfield node)
    (ids : List ℕ) (hn : ids.Nodup)
    (hh : ∀ id < (AssignmentConcrete.weightedHashes q).length, id ∈ ids)
    (hm : q.marked = true → (AssignmentConcrete.weightedHashes q).length ∈ ids)
    (color : ℕ → Fin r)
    (hslot : ∀ f ∈ ids, ∀ j (hj : (j, n + f) ∈ q.ps),
      (q.packing.label (planIndex q.ps n f j hj)).slot 0 node = color f)
    (hzero : ∀ id j (v : Fin n), v ∈ H →
      PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v = 0)
    (hhash : ∀ id ∈ ids, ∀ hi : id < (AssignmentConcrete.weightedHashes q).length,
      ∀ w ∈ (AssignmentConcrete.weightedHashes q)[id], ∀ l ∈ w.literals,
        l.variable ∉ H → (l.variable.val, n + id) ∈ q.ps)
    (hmark : q.marked = true → (AssignmentConcrete.weightedHashes q).length ∈ ids →
      ∀ l ∈ q.markedClause, l.variable ∉ H →
        (l.variable.val, n + (AssignmentConcrete.weightedHashes q).length) ∈ q.ps)
    (key : (i : ℕ) → Fin (count i) → K i)
    (enumerate : ∀ g : Fin r, Fin (count g.val) ≃
      (Head (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool))
    (hkernel : ∀ g i j, key g.val i = key g.val j ↔
      freeLabel q.p q.ps q.packing owner head H node g (enumerate g i) =
        freeLabel q.p q.ps q.packing owner head H node g (enumerate g j)) :
    (∑ E ∈ Finset.univ.filter (fun E : Finset (ResidualEmbedding.Free H) => E.card < q.J),
      ∑ U ∈ E.powerset, ((-1 : ℤ) ^ (E.card - U.card)) •
        ∑ reps : Prefix (Representatives key) r,
          Dense.readout (∏ g,
            ∑ x : Head (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool,
              if freeLabel q.p q.ps q.packing owner head H node g x =
                  freeLabel q.p q.ps q.packing owner head H node g (enumerate g (reps g).val) ∧
                  (∀ v : Head (fun v : ResidualEmbedding.Free H => head node v.val) g,
                    v.val ∈ E → x v = true) then
                QueryEvaluation.specializeDense q.p.t q.J (fun v => decide (v ∈ U))
                  (sourceProduct q H high
                    (stateFor H high (assemble (fun v : ResidualEmbedding.Free H => head node v.val)
                      (Function.update (fun h => enumerate h (reps h).val) g x)))
                    (ids.filter (fun f => color f = g)))
              else 0)) =
      Truncated.ofPolynomial q.J ((specTarget q H high).comp
        (X + C (q.p.ops.decode q.theta))) := by
  let A := fun (g : Fin r) (x : ResidualEmbedding.Free H → Bool) =>
    sourceProduct q H high (stateFor H high x) (ids.filter (fun f => color f = g))
  let label := freeLabel q.p q.ps q.packing owner head H node
  have hlocal (U : Finset (ResidualEmbedding.Free H)) (g : Fin r)
      (x z : ResidualEmbedding.Free H → Bool)
      (hown : split (fun v : ResidualEmbedding.Free H => head node v.val) x g =
        split (fun v : ResidualEmbedding.Free H => head node v.val) z g)
      (hother : ∀ h, h ≠ g →
        label h (split (fun v : ResidualEmbedding.Free H => head node v.val) x h) =
          label h (split (fun v : ResidualEmbedding.Free H => head node v.val) z h)) :
      QueryEvaluation.specializeDense q.p.t q.J (fun v => decide (v ∈ U)) (A g x) =
        QueryEvaluation.specializeDense q.p.t q.J (fun v => decide (v ∈ U)) (A g z) := by
    have h := colored_source_hlocal q owner howner head hhead H high node
      htheta ids color hslot (fun v => decide (v ∈ U)) g x z hown hother
    exact Eq.mp (congrArg (fun u =>
      QueryEvaluation.specializeDense u q.J (fun v => decide (v ∈ U)) (A g x) =
        QueryEvaluation.specializeDense u q.J (fun v => decide (v ∈ U)) (A g z)) hu) h
  have hgroup := QueryTupleReadoutSemantics.grouped_dense_query_emitted q.p.t q.J
    (fun v : ResidualEmbedding.Free H => head node v.val) key enumerate label hkernel A
    (fun x => colored_source_admissible q H high (stateFor H high x) ids color) hlocal
  have htarget : Dense.readout (∑ x, QueryEvaluation.specializeDense q.p.t q.J x (∏ g, A g x)) =
      Truncated.ofPolynomial q.J ((specTarget q H high).comp
        (X + C (q.p.ops.decode q.theta))) := by
    simp only [map_prod]
    exact QueryJetSemantics.colored_residual_target_dense_shift q hu H high
      (stateFor H high) (stateFor_get H high) ids hn hh hm color hzero hhash hmark
  exact hgroup.symm.trans htarget

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySourceTarget
