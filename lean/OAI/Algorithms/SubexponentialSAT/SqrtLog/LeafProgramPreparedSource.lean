import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceParametersBytes
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeAddressedQuery
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorSpec
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeConstants
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryRingModel

namespace OAI.Algorithms

/-! The source parameter object is derived from the executed query's numeric
bank, ring setup, and native head cache. Source order and jet order remain distinct. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native NativeSemantics
noncomputable section

def numeric (q : LeafQueryFrontend.Query) (k : ℕ) (l : Fin 8 → ℕ) :=
  Execute.guardedModel (q.input k) l

theorem numeric_Q (q : LeafQueryFrontend.Query) (k : ℕ) (l : Fin 8 → ℕ) :
    (numeric q k l).val 21=(produce (q.input k)).Q :=
  (Execute.guardedModel_public (q.input k) l 4).trans (Layout.model_core_values (q.input k) l).2.2.2.2.1

theorem numeric_R (q : LeafQueryFrontend.Query) (k : ℕ) (l : Fin 8 → ℕ) :
    (numeric q k l).val 29=(produce (q.input k)).R :=
  (Execute.guardedModel_public (q.input k) l 6).trans (Layout.model_core_values (q.input k) l).2.2.2.2.2.2.1

theorem numeric_t (q : LeafQueryFrontend.Query) (k : ℕ) (l : Fin 8 → ℕ)
    (hg : Guard (q.input k)) : (numeric q k l).val 33=(produce (q.input k)).t :=
  Execute.guardedModel_precision _ _ (Nat.ne_of_gt hg.2.2.1)

theorem numeric_d (q : LeafQueryFrontend.Query) (k : ℕ) (l : Fin 8 → ℕ)
    (hg : Guard (q.input k)) : (numeric q k l).val 34=(produce (q.input k)).d := by
  apply Execute.guardedModel_degree
  have h := hg.2.2.2.2.2.2.1
  omega

theorem numeric_J (q : LeafQueryFrontend.Query) (k : ℕ) (l : Fin 8 → ℕ)
    (hg : Guard (q.input k)) : (numeric q k l).val 42=(produce (q.input k)).J := by
  apply (Execute.guardedModel_public (q.input k) l 11).trans
  apply Layout.model_jet _ _ (Nat.ne_of_gt hg.2.2.1)
  have h := hg.2.2.2.2.2.2.1
  omega

theorem numeric_field (q : LeafQueryFrontend.Query) (k : ℕ) (l : Fin 8 → ℕ)
    (hg : Guard (q.input k)) : (produce (q.input k)).Q < 3^((numeric q k l).val 34) := by
  rw [numeric_d q k l hg]
  exact extensionDegree_sufficient _

variable (q : LeafQueryFrontend.Query) (k : ℕ) (hg : Guard (q.input k))
    (first : Word (Query.packingProblem q k hg).r (Query.packingProblem q k hg).Q)
    (tail : List (Word (Query.packingProblem q k hg).r (Query.packingProblem q k hg).Q))
    (node : Fin (Query.packingProblem q k hg).Q)
    (l : Fin 8 → ℕ)

abbrev heads := LeafHeadSetupProgram.Native.queryInputsAddressed q k hg first tail node

def parameters (words : List (List Bool))
    (hc : LeafHeadSetupProgram.CacheCorrect (heads q k hg first tail node).height
      (LeafHeadSetupProgram.unary (heads q k hg first tail node).R)
      (heads q k hg first tail node).width words)
    (M : SubexpPreparedQuartic.Modulus 3 ((numeric q k l).val 33))
    (cache : RingProgram.ScalarCache 3 ((numeric q k l).val 33))
    (half : RingProgram.ScalarCode 3 ((numeric q k l).val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced (numeric q k l) (Query.ring_degree_pos (q.input k) l hg)
      M cache half e) : SourceBank.Parameters (Query.packingProblem q k hg).r
        (Query.packingProblem q k hg).Q ((numeric q k l).val 34) :=
  SourceBank.Parameters.ofProduced (heads q k hg first tail node) words hc (numeric q k l)
    (Query.ring_precision_pos (q.input k) l hg) (Query.ring_degree_pos (q.input k) l hg)
    M cache half e hp (numeric_field q k l hg)

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
