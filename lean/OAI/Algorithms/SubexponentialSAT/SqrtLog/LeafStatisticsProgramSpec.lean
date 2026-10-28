import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpIncidenceSlotProgram

namespace OAI.Algorithms

/-! Pure specifications for the native residual statistics scans. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram
abbrev degree := Subexp.IncidencePlanSpec.degree
abbrev scopeBits := SubexpIncidenceSlotProgram.scopeBits

structure Totals where
  free : ℕ
  occurrence : ℕ
  incidences : ℕ
  uncovered : ℕ
  deriving DecidableEq, Repr

def Totals.add (t : Totals) (d : ℕ) : Totals :=
  ⟨t.free+1,max (max 1 d) t.occurrence,t.incidences+max 1 d,
    t.uncovered+(if d=0 then 1 else 0)⟩

def variableTotals (scopes : List (List ℕ)) : ℕ → List Bool → Totals → Totals
  | _,[],t => t
  | v,b::bs,t => variableTotals scopes (v+1) bs (if b then t else t.add (degree scopes v))

namespace Scope
def low (mask : List Bool) (v : ℕ) : Bool := !(mask[v]?.getD true)
end Scope

namespace Arity
def arity (mask : List Bool) (scopes : List (List ℕ)) (a : ℕ) :=
  scopes.foldl (fun t scope => max (scope.filter (Scope.low mask)).length t) a

end Arity
end SubexponentialSAT.SqrtLog.LeafStatisticsProgram

end OAI.Algorithms
