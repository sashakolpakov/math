import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedFactorFields

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics
noncomputable section

variable (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (first : Word (Query.packingProblem q k hg).r (Query.packingProblem q k hg).Q)
    (tail : List (Word (Query.packingProblem q k hg).r (Query.packingProblem q k hg).Q))
    (node : Fin (Query.packingProblem q k hg).Q) (l : Fin 8 → ℕ)
    (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect (heads q k hg first tail node).height
      (LeafHeadSetupProgram.unary (heads q k hg first tail node).R)
      (heads q k hg first tail node).width words)
    (M : SubexpPreparedQuartic.Modulus 3 ((numeric q k l).val 33))
    (cache : RingProgram.ScalarCache 3 ((numeric q k l).val 33))
    (half : RingProgram.ScalarCode 3 ((numeric q k l).val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced (numeric q k l) (Query.ring_degree_pos (q.input k) l hg)
      M cache half e)
    (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hsource : q.clauses=HashInputProgram.Expansion.encodedClauses source)

abbrev sourceParameters := parameters q k hg first tail node l words hc M cache half e hp

def nativeSpec : Factor.Spec (Query.packingProblem q k hg).r (Query.packingProblem q k hg).Q
    (Query.packingProblem q k hg).n ((numeric q k l).val 34) :=
  nativeSpecOfInputs (heads q k hg first tail node) (numeric q k l)
    (Query.ring_precision_pos (q.input k) l hg) (Query.ring_degree_pos (q.input k) l hg)
    words hc M cache half e hp (numeric_field q k l hg) q hv
    (produce (q.input k)).J (produce_J_pos (q.input k)) source hsource

theorem nativeSpec_code :
    e.stacks 281=RingProgram.flat (nativeSpec q k hg first tail node l words hc M cache half e hp hv source hsource).code :=
  nativeSpecOfInputs_code (heads q k hg first tail node) (numeric q k l)
    (Query.ring_precision_pos (q.input k) l hg) (Query.ring_degree_pos (q.input k) l hg)
    words hc M cache half e hp (numeric_field q k l hg) q hv
    (produce (q.input k)).J (produce_J_pos (q.input k)) source hsource

-- The theta identity is supplied by nativeSpecOfInputs_theta; keeping it
-- generic avoids expanding the complete numeric model in a dependent type.

theorem nativeSpec_rows :
    Encoding.encodeList id (nativeSpec q k hg first tail node l words hc M cache half e hp hv source hsource).rawRows=
      HashScopeProgram.RawTable.inputBits q.width.length q.rows :=
  nativeSpecOfInputs_rows (heads q k hg first tail node) (numeric q k l)
    (Query.ring_precision_pos (q.input k) l hg) (Query.ring_degree_pos (q.input k) l hg)
    words hc M cache half e hp (numeric_field q k l hg) q hv
    (produce (q.input k)).J (produce_J_pos (q.input k)) source hsource

theorem nativeSpec_parameters :
    (nativeSpec q k hg first tail node l words hc M cache half e hp hv source hsource).u=(numeric q k l).val 33 ∧
    (nativeSpec q k hg first tail node l words hc M cache half e hp hv source hsource).J=(produce (q.input k)).J ∧
    (nativeSpec q k hg first tail node l words hc M cache half e hp hv source hsource).p.R=(produce (q.input k)).R ∧
    (nativeSpec q k hg first tail node l words hc M cache half e hp hv source hsource).p.aWord.length=
      TailInterval.intervalStart (produce (q.input k)).r (produce (q.input k)).Q (produce (q.input k)).R := by
  have h := nativeSpecOfInputs_parameters (heads q k hg first tail node) (numeric q k l)
    (Query.ring_precision_pos (q.input k) l hg) (Query.ring_degree_pos (q.input k) l hg)
    words hc M cache half e hp (numeric_field q k l hg) q hv
    (produce (q.input k)).J (produce_J_pos (q.input k)) source hsource
  exact ⟨h.1,h.2.1,h.2.2.1,(congrArg List.length h.2.2.2).trans List.length_replicate⟩

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
