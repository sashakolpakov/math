import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorReadyCaps
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorBoundsIncidence

namespace OAI.Algorithms

/-! The source cap is computed from physical live-word and incidence sizes.
This eliminates the independent size choice in FactorReady.Limits. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorResource
open SubexponentialSAT SubexpLiftRing
open SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open PerturbationAssembly

def sourceCap {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A T F : ℕ) : ℕ :=
  sourceCallWordBound (FactorReady.callBound q A T F) n
    (incidenceBitsBound n q.J (d*baseWidth 3 q.p.t))+
    FactorReady.callBound q A T F+n+F+(LayoutOwnerFiberProgram.stream q.ps).length+1

theorem sourceCap_limits {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A T F : ℕ) :
    FactorReady.Limits q (sourceCap q A T F) A T F := by
  constructor <;> unfold sourceCap <;> omega

theorem callBound_le {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A T F X : ℕ)
    (hA : A ≤ X) (hT : T ≤ X) (hF : F ≤ X)
    (hseed : FactorReady.seedBound n (baseWidth 3 q.p.t) d q.u q.J ≤ X)
    (hpayload : FactorReady.payloadBound q.rawRows q.clauses ≤ X) :
    FactorReady.callBound q A T F ≤ 5*X+1 := by
  unfold FactorReady.callBound FactorReady.wordBound
  omega

/-- The actual complete source-incidence table appears in this cap; it is
not included among quantities claimed polynomial in original input bits. -/
theorem sourceCap_le {r Q n d : ℕ} (q : Factor.Spec r Q n d) (A T F X : ℕ)
    (hA : A ≤ X) (hT : T ≤ X) (hF : F ≤ X) (hn : n ≤ X)
    (hseed : FactorReady.seedBound n (baseWidth 3 q.p.t) d q.u q.J ≤ X)
    (hpayload : FactorReady.payloadBound q.rawRows q.clauses ≤ X)
    (htable : n*literalRecordBound n (incidenceBitsBound n q.J (d*baseWidth 3 q.p.t)) ≤ X)
    (hplans : (LayoutOwnerFiberProgram.stream q.ps).length ≤ X) :
    sourceCap q A T F ≤ 15*X+4 := by
  have hc := callBound_le q A T F X hA hT hF hseed hpayload
  unfold sourceCap sourceCallWordBound
  omega

theorem payloadBound_le_inputs (rows clauses : List (List Bool)) :
    FactorReady.payloadBound rows clauses ≤
      (Encoding.encodeList id rows).length+(Encoding.encodeList id clauses).length := by
  have h (xs : List (List Bool)) : (xs.map List.length).sum ≤ (Encoding.encodeList id xs).length := by
    induction xs with
    | nil => simp [Encoding.encodeList]
    | cons x xs ih =>
        simp only [List.map_cons,List.sum_cons,Encoding.length_encodeList_cons,id_eq]
        omega
  exact Nat.add_le_add (h rows) (h clauses)

end SubexponentialSAT.SqrtLog.LeafProgram.FactorResource

end OAI.Algorithms
