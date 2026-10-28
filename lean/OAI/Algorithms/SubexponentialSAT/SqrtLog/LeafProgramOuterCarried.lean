import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplay

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.OuterCarried

/-- Outer marked-branch and residual accumulators are not node-worker inputs. -/
def hidden (i : Fin 768) : Prop := i ∈ ([320, 322, 332] : List (Fin 768))

instance : DecidablePred hidden := fun i => inferInstanceAs (Decidable (i ∈ ([320, 322, 332] : List (Fin 768))))

end SubexponentialSAT.SqrtLog.LeafProgram.OuterCarried

end OAI.Algorithms
