import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingProgramInput

namespace OAI.Algorithms

/-! Runtime input data and explicit budgets for the physical packing frontend. -/
namespace SubexponentialSAT.Subexp.PackingFrontend

structure Params where
  D : ℕ
  Δ : ℕ
  scopes : List (List ℕ)
  rows : List (List Bool)
  width : List Bool
  alphabet : List (List Bool)

namespace Params

def input (p : Params) : PackingProgram.Input :=
  ⟨p.rows.flatten,p.width,List.replicate p.D true,List.replicate p.Δ true,
    SubexpPlanAlphabetBase.scopeBytes p.scopes,ProgramEncoding.encodeRecords p.alphabet⟩

def planList (p : Params) : List (List ℕ) :=
  (List.finRange p.D).map (fun v => IncidencePlanSpec.vertexPlan p.D p.Δ p.scopes v.val)

def planStream (p : Params) : List Bool :=
  ProgramEncoding.encodeRecords (SubexpPlanAlphabetBase.alphabet p.D p.Δ p.scopes)

def labelStream (p : Params) : List Bool :=
  BucketProgram.encodeRecords (PackingVertexLabels.labelRecords p.rows p.planList 0).reverse

def typeRows (p : Params) : List (List Bool) :=
  TupleProgram.powerRows p.alphabet (p.Δ+1) [[]]

def typeStream (p : Params) : List Bool := ProgramEncoding.encodeRecords p.typeRows

@[simp] theorem planList_length (p : Params) : p.planList.length=p.D := by simp [planList]

theorem planStream_eq (p : Params) :
    p.planStream = ProgramEncoding.encodeRecords (p.planList.map PackingVertexLabels.planPayload) := by
  rw [planStream,PackingVertexLabels.alphabet_eq_planPayload]
  rfl

def plansBound (p : Params) : ℕ :=
  SubexpPlanAlphabetBase.totalBound p.D p.Δ p.scopes+
    9*(SubexpPlanAlphabetBase.scopeBytes p.scopes).length+11*p.D+9*p.Δ+6*p.planStream.length+34

def labelsBound (p : Params) : ℕ :=
  PackingVertexLabels.traceCost p.width.length p.planList 0+
    9*p.rows.flatten.length+9*p.width.length+6*p.planStream.length+6*p.labelStream.length+2*p.D+31

def typesBound (p : Params) : ℕ :=
  UniversalTypeProgram.budget p.alphabet p.Δ+
    9*(ProgramEncoding.encodeRecords p.alphabet).length+7*p.Δ+6*p.typeStream.length+24

def bound (p : Params) : ℕ := p.plansBound+p.labelsBound+p.typesBound

end Params
end SubexponentialSAT.Subexp.PackingFrontend

end OAI.Algorithms
