import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteBucketLocality

namespace OAI.Algorithms

/-! Source identities for the actual merged assignment reference. Only low
literal incidences need a source entry; high literals use their fixed bits. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open Polynomial
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open DensePolynomialProgram LayoutProgram PerturbationAssembly MomentsAssembly
open BucketTupleProgram.Concrete

variable {r Q d n : ℕ}

theorem fixedSourceRow_high_zero (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (howner : ∀ i,(ps.get i).1=(owner i).val)
    (H : Finset (Fin n)) (hlow : ∀ i,owner i∉H) (f j : ℕ) (v : Fin n) (hv : v∈H) :
    fixedSourceRow p ps P n f j v=0 := by
  apply fixedSourceRow_zero p ps P n f j v
  intro a ha he
  obtain ⟨i,hi,hia⟩ := List.mem_iff_getElem.mp ha
  have ho := howner ⟨i,hi⟩
  simp only [List.get_eq_getElem,hia] at ho
  have hev : owner ⟨i,hi⟩=v := Fin.ext (ho.symm.trans he)
  exact hlow ⟨i,hi⟩ (hev.symm ▸ hv)

theorem factorJet_eval_branch_low (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (H : Finset (Fin n)) (high : H → Bool)
    (theta : Coeff (baseWidth 3 p.t) d) (state : Fin 768 → List Bool)
    (x : ResidualEmbedding.Free H → Bool) (f : ℕ) (j : Fin n)
    (hpresent : j∉H → (j.val,n+f)∈ps)
    (hmask : (state 702).getD j.val false=decide (j∈H))
    (hhigh : ∀ hj:j∈H,(state 703).getD j.val false=high ⟨j,hj⟩)
    (hzero : ∀ v∈H,fixedSourceRow p ps P n f j.val v=0)
    (hbase : j∉H → baseline (n:=n) p ps P theta state f j.val =
      ∑ v : ResidualEmbedding.Free H,
        (fixedSourceRow p ps P n f j.val v.val).eval (p.ops.decode theta)*HashInput.boolValue (x v)) :
    Moments.jetEval (Squarefree.boolValue (HighIncidence.glue H high x))
      (Squarefree.boolValue_idempotent (HighIncidence.glue H high x))
      (Factor.factorJet p ps P n f j.val theta state) =
    C ((NodeSemantics.branchPath H high (completedRows p ps P H) x f j).comp
      (X+C (p.ops.decode theta))) := by
  by_cases hj : j∈H
  · rw [factorJet_embedding p ps P H high theta state f j hmask hhigh hzero,
      ResidualEmbedding.eval_jet_branch]
    simp only [residualJet,NodeSemantics.jetEval_ringScalar,
      NodeSemantics.branchPath,dite_eq_left hj,Polynomial.C_comp]
  · exact factorJet_eval_branch p ps P H high theta state x f j (hpresent hj) hmask hhigh hzero hbase

theorem merged_factorJet_eval (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (howner : ∀ i,(ps.get i).1=(owner i).val)
    (head : Fin Q → Fin n → Fin r) (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (H : Finset (Fin n)) (hlow : ∀ i,owner i∉H) (high : H → Bool) (t : Fin Q)
    {tables : Fin r → BucketTupleProgram.HeadTable}
    (s : ∀ g,HeadSemantics H (fun v=>head t v.val) g ps.length
      (LayoutProducedMatrix.literalNat P owner p.aWord.length p.R t) (tables g))
    (y : ∀ g,Moments.LabelValue (fun g=>(s g).label) g)
    (a : ∀ g,Moments.LabelBucket (fun g=>(s g).label) g (y g))
    (hm : ∀ g,(tables g).mask=List.ofFn (headMask H (fun v=>head t v.val) g))
    (theta : Coeff (baseWidth 3 p.t) d)
    (htheta : p.ops.decode theta=p.model.node p.t Q p.ht p.hfield t)
    (mask bits : List Bool)
    (hmask : ∀ v : Fin n,mask.getD v.val false=decide (v∈H))
    (hbits : ∀ v : H,bits.getD v.val.val false=high v)
    (support : List Bool) (f : ℕ) (j : Fin n) (g : Fin r)
    (hpresent : j∉H → (j.val,n+f)∈ps)
    (hg : ∀ hj:j∉H,(P.label (planIndex ps n f j.val (hpresent hj))).slot 0 t=g) :
    Moments.jetEval
      (Squarefree.boolValue (HighIncidence.glue H high
        (Moments.assemble (fun v=>head t v.val) (fun k=>(a k).val))))
      (Squarefree.boolValue_idempotent _)
      (Factor.factorJet p ps P n f j.val theta
        (FactorLoop.assignmentReference mask bits
          ⟨support,((s g).input (y g)).mask,((s g).input (y g)).context,(familyInput s y).context⟩
          ((s g).encode (a g).val))) =
    C ((NodeSemantics.branchPath H high (completedRows p ps P H)
      (Moments.assemble (fun v=>head t v.val) (fun k=>(a k).val)) f j).comp
      (X+C (p.ops.decode theta))) := by
  apply factorJet_eval_branch_low p ps P H high theta _ _ f j hpresent
  · simpa [FactorLoop.assignmentReference] using hmask j
  · intro hj
    simpa [FactorLoop.assignmentReference] using hbits ⟨j,hj⟩
  · exact fixedSourceRow_high_zero p ps P owner howner H hlow f j.val
  · intro hj
    exact merged_baseline_eq p ps P owner howner head hhead H t s y a hm theta htheta
      mask bits support f j.val (hpresent hj)
      (fixedSourceRow_high_zero p ps P owner howner H hlow f j.val) g (hg hj)

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
